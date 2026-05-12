## Quick Start

### 1. Start the Python server (Terminal 1)
```
python3 bandit_server.py --alpha 1.5 --epsilon 0.6
```

### 2. Run Cubicle (Terminal 2)
```
./cubicle.opt examples/dispatch/dispatch_dekker.cub -int-brab 3 -fuzz-limit 10000 5 5
```

### 3. That's it
CFL connects to the server automatically. If the server isn't running, CFL falls back to random.

## Options
```
--alpha FLOAT    Exploration parameter (default 1.5)
--epsilon FLOAT  Forced random rate (default 0.2, best so far: 0.6)
--warmup INT     Rounds per arm before learning starts (default 3)
--save-on-exit PATH   Save learned model on exit
--load PATH           Load a previously saved model
```

## Experiments
Kill and restart the server between runs for independent results.

## Alpha & Epsilon

**Alpha** controls how much the bandit favors heuristics it hasn't tried much. High alpha means "try uncertain things more," low alpha means "stick with what I know works." Range: 0.5 to 3.0.

**Epsilon** is the probability that the bandit ignores its learned model and picks a random heuristic instead. Epsilon=0.0 means pure LinUCB, epsilon=1.0 means pure random. 
E.g. 0.6 = 60% of picks are random and 40% are guided by the learned model. 