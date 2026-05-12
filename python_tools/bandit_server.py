"""
LinUCB Contextual Bandit Server for CFL Strategy Selection
==========================================================

This server replaces the random strategy selection in CFL's main loop
(continue_from_bfs) with a contextual bandit that learns which exploration
strategy works best given the current state of the exploration.

Algorithm: LinUCB (Li et al., 2010)
    For each arm (strategy), we maintain a linear model that predicts
    reward from context features. The Upper Confidence Bound (UCB)
    balances exploitation (pick what worked before) with exploration
    (try uncertain arms). Over time, the bandit converges toward
    choosing the best strategy for each situation.

Arms (6 CFL strategies):
    0: run_forward        - Random exploration
    1: markov_entropy     - Maximize entropy/randomness
    2: force_procs_forward - Force one process forward
    3: do_new_exit        - Cover an unused exit transition
    4: run_smart          - Weighted decision (novelty-based)
    5: further_bfs        - Limited BFS

Context features (extracted from the CFL node + global state):
    - node_seen:           how many times this node has been visited
    - exit_number:         total exit transitions from this node
    - exit_remaining_ratio: fraction of exits not yet taken (0.0 to 1.0)
    - log_visit_count:     log of total unique states found so far
    - log_pool_size:       log of current remaining pool size
    - pool_ratio:          visit_count / pool_size (exploration saturation)
    - bias:                constant 1.0 (intercept term)

Reward:
    new_seen — number of genuinely new states discovered during the
    explore() call. This directly measures what matters for BRAB.

Protocol (JSON over TCP):
    Select:  {"type": "select", "context": [f1, f2, ...]}
             -> {"arm": 3}

    Update:  {"type": "update", "arm": 3, "context": [f1, ...], "reward": 12}
             -> {"ok": true}

    Stats:   {"type": "stats"}
             -> {"pulls": [...], "rewards": [...], ...}

    Save:    {"type": "save", "path": "model.json"}
             -> {"ok": true}

    Load:    {"type": "load", "path": "model.json"}
             -> {"ok": true}

Usage:
    python bandit_server.py [--port PORT] [--alpha ALPHA] [--save-on-exit PATH]

References:
    Li, L., Chu, W., Langford, J., & Schapire, R. E. (2010).
    A contextual-bandit approach to personalized news article recommendation.
    WWW 2010.
"""

import socket
import json
import numpy as np
import argparse
import signal
import sys
import os
from datetime import datetime


# ============================================================================
# LinUCB Algorithm
# ============================================================================

class LinUCB:
    """
    LinUCB with disjoint linear models (one per arm).

    Each arm a maintains:
        A_a : (d x d) matrix  — roughly, the covariance of observed contexts
        b_a : (d,) vector     — roughly, the reward-weighted sum of contexts

    On select:
        theta_a = A_a^{-1} b_a           (estimated coefficients)
        ucb_a   = theta_a^T x + alpha * sqrt(x^T A_a^{-1} x)
        Pick arm with highest ucb_a.

    On update:
        A_a = A_a + x x^T
        b_a = b_a + reward * x
    """

    def __init__(self, n_arms, n_features, alpha=1.0, warmup_rounds=3, epsilon=0.2):
        """
        Parameters
        ----------
        n_arms : int
            Number of arms (strategies). For CFL, this is 6.
        n_features : int
            Dimension of the context vector.
        alpha : float
            Exploration parameter. Higher = more exploration.
            Start with 1.0, tune if needed. Values in [0.5, 2.0] are typical.
        warmup_rounds : int
            Number of times each arm must be tried before LinUCB kicks in.
            This prevents the cold-start problem where one lucky early arm
            dominates forever. Default 3 = each arm tried 3 times = 18 pulls
            before optimization begins.
        epsilon : float
            Probability of choosing a random arm instead of the UCB-optimal one.
            This forces strategy diversity, which is critical for CFL because
            BRAB success depends on finding the RIGHT states, not just the MOST.
            Default 0.2 = 20% random exploration.
        """
        self.n_arms = n_arms
        self.n_features = n_features
        self.alpha = alpha
        self.warmup_rounds = warmup_rounds
        self.epsilon = epsilon

        # Per-arm parameters
        self.A = [np.eye(n_features) for _ in range(n_arms)]
        self.b = [np.zeros(n_features) for _ in range(n_arms)]

        # Cached inverses (recomputed on update)
        self.A_inv = [np.eye(n_features) for _ in range(n_arms)]

        # Statistics for monitoring
        self.pulls = np.zeros(n_arms, dtype=int)
        self.total_reward = np.zeros(n_arms)
        self.history = []  # List of (context, arm, reward) for analysis

    def select(self, context):
        """
        Choose an arm given a context vector.

        During the warmup phase, arms are selected round-robin so that
        each arm gets at least warmup_rounds pulls. After warmup,
        LinUCB selects based on Upper Confidence Bounds.

        Parameters
        ----------
        context : np.ndarray of shape (n_features,)

        Returns
        -------
        arm : int
            Index of the chosen arm.
        ucb_scores : list of float
            UCB score for each arm (useful for logging/debugging).
        """
        x = np.asarray(context, dtype=float)

        # Warmup: round-robin until every arm has been tried warmup_rounds times
        min_pulls = int(np.min(self.pulls))
        if min_pulls < self.warmup_rounds:
            # Find the arm with the fewest pulls (break ties randomly)
            least_pulled = np.where(self.pulls == min_pulls)[0]
            arm = int(np.random.choice(least_pulled))
            return arm, [0.0] * self.n_arms

        # Epsilon-greedy: with probability epsilon, pick a random arm
        # This forces strategy diversity, which is essential because
        # BRAB needs diverse states, not just many states.
        if np.random.random() < self.epsilon:
            arm = int(np.random.randint(self.n_arms))
            return arm, [0.0] * self.n_arms

        # LinUCB selection
        ucb_scores = np.zeros(self.n_arms)

        for a in range(self.n_arms):
            theta_a = self.A_inv[a] @ self.b[a]
            exploitation = theta_a @ x
            exploration = self.alpha * np.sqrt(x @ self.A_inv[a] @ x)
            ucb_scores[a] = exploitation + exploration

        arm = int(np.argmax(ucb_scores))
        return arm, ucb_scores.tolist()

    def update(self, arm, context, reward):
        """
        Update the model for a given arm after observing a reward.

        Parameters
        ----------
        arm : int
            The arm that was pulled.
        context : np.ndarray of shape (n_features,)
        reward : float
            Observed reward (new_seen for CFL).
        """
        x = np.asarray(context, dtype=float)

        # A_a = A_a + x x^T
        self.A[arm] += np.outer(x, x)

        # b_a = b_a + reward * x
        self.b[arm] += reward * x

        # Recompute inverse for this arm
        # For production with very high-dimensional contexts, you'd use
        # the Sherman-Morrison formula. For d=7, direct inverse is fine.
        self.A_inv[arm] = np.linalg.inv(self.A[arm])

        # Update statistics
        self.pulls[arm] += 1
        self.total_reward[arm] += reward
        self.history.append({
            "context": x.tolist(),
            "arm": arm,
            "reward": reward,
        })

    def get_stats(self):
        """Return human-readable statistics."""
        arm_names = [
            "random", "entropy", "proc_seq",
            "new_exit", "smart", "bfs"
        ]
        stats = {
            "total_pulls": int(np.sum(self.pulls)),
            "arms": {}
        }
        for a in range(self.n_arms):
            avg = (self.total_reward[a] / self.pulls[a]
                   if self.pulls[a] > 0 else 0.0)
            stats["arms"][arm_names[a]] = {
                "pulls": int(self.pulls[a]),
                "total_reward": float(self.total_reward[a]),
                "avg_reward": round(avg, 3),
            }
        return stats

    def save(self, path):
        """Save learned parameters to a JSON file (for warm-starting later)."""
        data = {
            "n_arms": self.n_arms,
            "n_features": self.n_features,
            "alpha": self.alpha,
            "A": [a.tolist() for a in self.A],
            "b": [b.tolist() for b in self.b],
            "pulls": self.pulls.tolist(),
            "total_reward": self.total_reward.tolist(),
            "saved_at": datetime.now().isoformat(),
        }
        with open(path, 'w') as f:
            json.dump(data, f, indent=2)

    def load(self, path):
        """Load previously saved parameters (warm start)."""
        with open(path, 'r') as f:
            data = json.load(f)

        if data["n_arms"] != self.n_arms:
            raise ValueError(
                f"Saved model has {data['n_arms']} arms, "
                f"expected {self.n_arms}"
            )
        if data["n_features"] != self.n_features:
            raise ValueError(
                f"Saved model has {data['n_features']} features, "
                f"expected {self.n_features}"
            )

        for a in range(self.n_arms):
            self.A[a] = np.array(data["A"][a])
            self.b[a] = np.array(data["b"][a])
            self.A_inv[a] = np.linalg.inv(self.A[a])

        self.pulls = np.array(data["pulls"], dtype=int)
        self.total_reward = np.array(data["total_reward"])


# ============================================================================
# Context Feature Engineering
# ============================================================================

def build_context(raw_context):
    """
    Transform raw CFL features into the context vector for LinUCB.

    The raw context from OCaml contains:
        [node_seen, exit_number, exit_remaining, visit_count, pool_size, overall,
         total_transitions, covered_transitions]

    We engineer features that are:
        - Normalized (so different scales don't dominate)
        - Informative (ratios and logs capture relative progress)
        - System-agnostic (no model-specific features)

    Parameters
    ----------
    raw_context : list of numbers
        Raw features sent by OCaml.

    Returns
    -------
    context : np.ndarray of shape (N_FEATURES,)
    """
    node_seen = raw_context[0]
    exit_number = raw_context[1]
    exit_remaining = raw_context[2]
    visit_count = max(raw_context[3], 1)
    pool_size = max(raw_context[4], 1)
    overall = max(raw_context[5], 1)
    total_tr = max(raw_context[6], 1) if len(raw_context) > 6 else 1
    covered_tr = raw_context[7] if len(raw_context) > 7 else 0

    # Feature 1: Node familiarity (how "explored" is this node?)
    # Log to compress — a node seen 100 times isn't 100x different from seen once
    node_familiarity = np.log1p(node_seen)

    # Feature 2: Exit richness (how many choices does this node offer?)
    exit_richness = np.log1p(exit_number)

    # Feature 3: Exit remaining ratio (how much is unexplored from here?)
    # 1.0 = nothing explored, 0.0 = everything taken
    exit_remaining_ratio = (
        exit_remaining / exit_number if exit_number > 0 else 0.0
    )

    # Feature 4: Global exploration progress
    log_visit_count = np.log1p(visit_count)

    # Feature 5: Pool saturation (are we generating more starts than we use?)
    log_pool_size = np.log1p(pool_size)

    # Feature 6: Exploration efficiency
    # High ratio = we've found many unique states relative to pool size
    # Low ratio = pool is growing but not leading to discoveries
    pool_ratio = visit_count / pool_size

    # Feature 7: Transition coverage ratio (THE KEY FEATURE)
    # 0.0 = no transitions explored, 1.0 = all transitions have been fired
    # As this approaches 1.0, the bandit should shift away from random
    # toward strategies that target unexplored corners
    tr_coverage_ratio = covered_tr / total_tr

    # Feature 8: Bias term (intercept — lets the model learn a base preference)
    bias = 1.0

    return np.array([
        node_familiarity,
        exit_richness,
        exit_remaining_ratio,
        log_visit_count,
        log_pool_size,
        pool_ratio,
        tr_coverage_ratio,
        bias,
    ])


N_ARMS = 6
N_FEATURES = 8  # Must match the length of build_context output


# ============================================================================
# TCP Server
# ============================================================================

class BanditServer:
    """
    Simple TCP server that wraps the LinUCB bandit.

    Handles JSON messages from the OCaml CFL client.
    One connection at a time (CFL is single-threaded).
    """

    def __init__(self, host, port, alpha, warmup=3, epsilon=0.2, save_path=None, load_path=None):
        self.host = host
        self.port = port
        self.save_path = save_path

        self.bandit = LinUCB(
            n_arms=N_ARMS,
            n_features=N_FEATURES,
            alpha=alpha,
            warmup_rounds=warmup,
            epsilon=epsilon,
        )

        # Warm start from saved parameters if requested
        if load_path and os.path.exists(load_path):
            print(f"Loading saved parameters from {load_path}")
            self.bandit.load(load_path)
            stats = self.bandit.get_stats()
            print(f"  Loaded model with {stats['total_pulls']} prior pulls")

        # Keep track of last context for convenience
        # (OCaml sends context on select, reward on update)
        self.last_context = None

    def handle_message(self, msg):
        """
        Process a single JSON message and return a JSON response.

        Parameters
        ----------
        msg : dict
            Parsed JSON message from OCaml.

        Returns
        -------
        response : dict
            JSON-serializable response to send back.
        """
        msg_type = msg.get("type")

        if msg_type == "select":
            raw_ctx = msg["context"]
            ctx = build_context(raw_ctx)
            self.last_context = ctx
            arm, scores = self.bandit.select(ctx)

            arm_names = ["random", "entropy", "proc_seq",
                         "new_exit", "smart", "bfs"]
            min_pulls = int(np.min(self.bandit.pulls))
            total = int(np.sum(self.bandit.pulls))
            if min_pulls < self.bandit.warmup_rounds:
                phase = "WARMUP"
            elif all(s == 0.0 for s in scores):
                phase = "ε-rand"
            else:
                phase = "LinUCB"
            print(f"  [{phase}] pull #{total+1}: {arm_names[arm]}", end="", flush=True)

            return {"arm": arm}

        elif msg_type == "update":
            arm = msg["arm"]
            reward = msg["reward"]

            print(f" -> reward={reward}")

            # Use context from the update message if provided,
            # otherwise fall back to the last select context
            if "context" in msg:
                ctx = build_context(msg["context"])
            elif self.last_context is not None:
                ctx = self.last_context
            else:
                return {"error": "No context available for update"}

            self.bandit.update(arm, ctx, reward)
            return {"ok": True}

        elif msg_type == "stats":
            return self.bandit.get_stats()

        elif msg_type == "save":
            path = msg.get("path", self.save_path or "bandit_model.json")
            self.bandit.save(path)
            return {"ok": True, "path": path}

        elif msg_type == "load":
            path = msg.get("path", "bandit_model.json")
            self.bandit.load(path)
            return {"ok": True}

        else:
            return {"error": f"Unknown message type: {msg_type}"}

    def run(self):
        """Start the server and listen for connections."""
        server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        server.bind((self.host, self.port))
        server.listen(1)

        print(f"Bandit server listening on {self.host}:{self.port}")
        print(f"  Arms: {N_ARMS} | Features: {N_FEATURES} | Alpha: {self.bandit.alpha}")
        print(f"  Warmup: {self.bandit.warmup_rounds} rounds per arm ({self.bandit.warmup_rounds * N_ARMS} total pulls before optimization)")
        print(f"  Epsilon: {self.bandit.epsilon} (random exploration rate after warmup)")
        print(f"  Waiting for CFL connection...")

        try:
            while True:
                conn, addr = server.accept()
                print(f"  Connected: {addr}")
                self.handle_connection(conn)
                print(f"  Disconnected: {addr}")

                # Print summary after each CFL run
                stats = self.bandit.get_stats()
                print(f"\n  Run summary ({stats['total_pulls']} pulls):")
                for name, info in stats["arms"].items():
                    if info["pulls"] > 0:
                        print(f"    {name:12s}: {info['pulls']:4d} pulls, "
                              f"avg reward {info['avg_reward']:.1f}")
                print()

        except KeyboardInterrupt:
            print("\nShutting down...")
        finally:
            if self.save_path:
                print(f"Saving model to {self.save_path}")
                self.bandit.save(self.save_path)
            server.close()

    def handle_connection(self, conn):
        """
        Handle a single TCP connection (one CFL run).

        Messages are newline-delimited JSON. This is simple, robust,
        and easy to implement on the OCaml side.
        """
        buffer = ""

        try:
            while True:
                data = conn.recv(4096)
                if not data:
                    break

                buffer += data.decode("utf-8")

                # Process all complete messages in the buffer
                while "\n" in buffer:
                    line, buffer = buffer.split("\n", 1)
                    line = line.strip()
                    if not line:
                        continue

                    try:
                        msg = json.loads(line)
                        response = self.handle_message(msg)
                    except json.JSONDecodeError:
                        response = {"error": "Invalid JSON"}
                    except Exception as e:
                        response = {"error": str(e)}

                    response_bytes = (json.dumps(response) + "\n").encode("utf-8")
                    conn.sendall(response_bytes)

        except (ConnectionResetError, BrokenPipeError):
            pass
        finally:
            conn.close()


# ============================================================================
# Entry Point
# ============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="LinUCB Contextual Bandit Server for CFL"
    )
    parser.add_argument(
        "--host", default="127.0.0.1",
        help="Host to bind to (default: 127.0.0.1)"
    )
    parser.add_argument(
        "--port", type=int, default=65432,
        help="Port to listen on (default: 65432)"
    )
    parser.add_argument(
        "--alpha", type=float, default=1.5,
        help="Exploration parameter (default: 1.5). "
             "Higher = more exploration. Range [0.5, 3.0] is typical."
    )
    parser.add_argument(
        "--warmup", type=int, default=3,
        help="Number of round-robin warmup rounds per arm (default: 3). "
             "Each arm is tried this many times before LinUCB kicks in. "
             "With 6 arms and warmup=3, that's 18 initial pulls."
    )
    parser.add_argument(
        "--epsilon", type=float, default=0.2,
        help="Probability of random arm choice (default: 0.2). "
             "Forces strategy diversity. 0.0 = pure LinUCB, 1.0 = pure random."
    )
    parser.add_argument(
        "--save-on-exit", type=str, default=None,
        help="Save learned parameters to this file on exit "
             "(for warm-starting future runs)"
    )
    parser.add_argument(
        "--load", type=str, default=None,
        help="Load previously saved parameters (warm start)"
    )

    args = parser.parse_args()

    server = BanditServer(
        host=args.host,
        port=args.port,
        alpha=args.alpha,
        warmup=args.warmup,
        epsilon=args.epsilon,
        save_path=args.save_on_exit,
        load_path=args.load,
    )

    # Handle SIGINT gracefully (save model if configured)
    def sigint_handler(sig, frame):
        print("\nInterrupted.")
        if args.save_on_exit:
            print(f"Saving model to {args.save_on_exit}")
            server.bandit.save(args.save_on_exit)
        sys.exit(0)

    signal.signal(signal.SIGINT, sigint_handler)

    server.run()


if __name__ == "__main__":
    main()