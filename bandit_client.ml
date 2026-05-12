(* 
   bandit_client.ml — TCP client for the LinUCB bandit server
   ===========================================================

   This module provides functions to communicate with the Python
   bandit server from OCaml. It replaces the random strategy selection
   in CFL's main loop (continue_from_bfs).

   Usage in interpret_fuzzy.ml:
   
   1. At the start of CFL, open a connection:
        let bandit_conn = Bandit_client.connect ()

   2. Replace:
        let choice = Random.int 7 in
      With:
        let ctx = Bandit_client.build_context
          ~node_seen:node.seen
          ~exit_number:node.exit_number
          ~exit_remaining:(List.length node.exit_remaining)
          ~v_count:!visit_count ~p_size:!pool_size ~overall_s:!overall in
        let choice = Bandit_client.select bandit_conn ctx

   3. After the explore call, send the reward:
        let new_seen = ... in  (* capture from the strategy function *)
        Bandit_client.update bandit_conn choice new_seen

   4. When CFL finishes, close the connection:
        Bandit_client.disconnect bandit_conn

   The strategies themselves are completely unchanged.
*)

let bandit_host = "127.0.0.1"
let bandit_port = 65432

(* Connection handle *)
type connection = {
  sock : Unix.file_descr;
  ic : in_channel;
  oc : out_channel;
}

(* ------------------------------------------------------------------ *)
(* Connection management                                               *)
(* ------------------------------------------------------------------ *)

let connect () =
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  let addr = Unix.ADDR_INET (Unix.inet_addr_of_string bandit_host, bandit_port) in
  begin
    try
      Unix.connect sock addr;
      Format.eprintf "Connected to bandit server at %s:%d@." bandit_host bandit_port
    with Unix.Unix_error (err, _, _) ->
      Format.eprintf "WARNING: Could not connect to bandit server (%s). Using random fallback.@."
        (Unix.error_message err);
      raise Exit
  end;
  let ic = Unix.in_channel_of_descr sock in
  let oc = Unix.out_channel_of_descr sock in
  { sock; ic; oc }

let disconnect conn =
  begin try Unix.close conn.sock with _ -> () end

(* ------------------------------------------------------------------ *)
(* JSON helpers (minimal, no external dependency)                      *)
(* ------------------------------------------------------------------ *)

(* We only need to produce simple JSON objects and parse {"arm": N}.
   No need for a full JSON library. *)

let send_json conn json_str =
  output_string conn.oc json_str;
  output_char conn.oc '\n';
  flush conn.oc

let recv_json conn =
  input_line conn.ic

(* Format a list of floats as a JSON array *)
let json_float_list lst =
  let strs = List.map (fun f -> Printf.sprintf "%.6f" f) lst in
  "[" ^ (String.concat ", " strs) ^ "]"

(* Extract an integer value for a given key from a simple JSON string.
   This is intentionally minimal — we only parse {"arm": 3} style responses.
   No dependency on Str. *)
let parse_int_field json_str field =
  let pattern = "\"" ^ field ^ "\"" in
  let pat_len = String.length pattern in
  let str_len = String.length json_str in
  try
    (* Find the pattern manually *)
    let rec search i =
      if i + pat_len > str_len then raise Not_found
      else if String.sub json_str i pat_len = pattern then i
      else search (i + 1)
    in
    let idx = search 0 in
    (* Skip past "field" and find the colon *)
    let after_key = idx + pat_len in
    let rec skip_to_colon i =
      if i >= str_len then raise Not_found
      else if json_str.[i] = ':' then i + 1
      else skip_to_colon (i + 1)
    in
    let after_colon = skip_to_colon after_key in
    let rest = String.sub json_str after_colon (str_len - after_colon) in
    Scanf.sscanf (String.trim rest) " %d" (fun n -> n)
  with _ ->
    Format.eprintf "WARNING: Could not parse field '%s' from: %s@." field json_str;
    -1

(* ------------------------------------------------------------------ *)
(* Context building                                                    *)
(* ------------------------------------------------------------------ *)

(* Build the raw context array to send to the Python server.
   The Python server handles feature engineering (logs, ratios, etc).
   
   We take plain values here (not the node record) because the
   record type is defined in interpret_fuzzy.ml. The caller extracts
   the fields and passes them in.

   Parameters:
     node_seen      — how many times this node has been visited
     exit_number    — total exit transitions from this node
     exit_remaining — how many exits have not yet been taken
     v_count        — current visit_count (total unique states)
     p_size         — current pool_size
     overall_s      — total steps taken
     total_tr       — total number of transitions in the model
     covered_tr     — how many transitions have been fired at least once
*)
let build_context ~node_seen ~exit_number ~exit_remaining
    ~v_count ~p_size ~overall_s ~total_tr ~covered_tr =
  [ float_of_int node_seen;
    float_of_int exit_number;
    float_of_int exit_remaining;
    float_of_int v_count;
    float_of_int (max p_size 1);
    float_of_int overall_s;
    float_of_int (max total_tr 1);
    float_of_int covered_tr ]

(* ------------------------------------------------------------------ *)
(* Bandit interaction                                                   *)
(* ------------------------------------------------------------------ *)

(* Ask the bandit which arm (strategy) to use.
   Returns an int in [0, 5] corresponding to the 6 CFL strategies.
   Returns -1 on communication error (caller should fall back to random). *)
let select conn context =
  let ctx_json = json_float_list context in
  let msg = Printf.sprintf "{\"type\": \"select\", \"context\": %s}" ctx_json in
  begin
    try
      send_json conn msg;
      let response = recv_json conn in
      parse_int_field response "arm"
    with _ ->
      Format.eprintf "WARNING: Bandit select failed, falling back to random@.";
      -1
  end

(* Inform the bandit about the result of the chosen strategy.
   arm     — which strategy was used (0-5)
   reward  — how many new states were discovered *)
let update conn arm reward =
  let msg = Printf.sprintf "{\"type\": \"update\", \"arm\": %d, \"reward\": %d}" arm reward in
  begin
    try
      send_json conn msg;
      let _response = recv_json conn in
      ()
    with _ ->
      Format.eprintf "WARNING: Bandit update failed@."
  end

(* Request a stats summary from the server (for logging/debugging). *)
let get_stats conn =
  let msg = "{\"type\": \"stats\"}" in
  begin
    try
      send_json conn msg;
      let response = recv_json conn in
      Format.eprintf "Bandit stats: %s@." response
    with _ ->
      Format.eprintf "WARNING: Could not get bandit stats@."
  end

(* Tell the server to save its learned parameters. *)
let save_model conn path =
  let msg = Printf.sprintf "{\"type\": \"save\", \"path\": \"%s\"}" path in
  begin
    try
      send_json conn msg;
      let _response = recv_json conn in
      Format.eprintf "Bandit model saved to %s@." path
    with _ ->
      Format.eprintf "WARNING: Could not save bandit model@."
  end