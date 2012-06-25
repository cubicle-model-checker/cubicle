(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

type mode = Dfs | DfsL | DfsH | DfsHL | Bfs | BfsDist | Bfsinvp

let usage = "usage: cubicle file.cub"
let file = ref " stdin"

let max_proc = 10
let type_only = ref false
let maxrounds = ref 100
let maxnodes = ref 100_000
let debug = ref false
let verbose = ref 0
let quiet = ref false

let incr_verbose () = incr verbose

let debug_smt = ref false
let dmcmt = ref false
let profiling = ref false

let only_forward = ref false
let gen_inv = ref false
let post_strategy = ref (-1)
let delete = ref true
let simpl_by_uc = ref false
let cores = ref 0

let mode = ref Bfs
let set_mode = function
  | "dfs" -> mode := Dfs
  | "dfsl" -> mode := DfsL
  | "dfsh" -> mode := DfsH
  | "dfshl" -> mode := DfsHL
  | "bfs" -> mode := Bfs
  | "bfsinvp" -> mode := Bfsinvp
  | _ -> raise (Arg.Bad "search strategy not supported")

let show_version () = Format.printf "%s@." Version.version; exit 0

let specs = 
  [ "-version", Arg.Unit show_version, " prints the version number";
    "-quiet", Arg.Set quiet, " do not output search trace";
    "-type-only", Arg.Set type_only, " stop after typing";
    "-depth", Arg.Set_int maxrounds, "<nb> max depth of the search tree (default 100)";
    "-nodes", Arg.Set_int maxnodes, "<nb> max number nodes to explore (default 100000)";
    "-search", Arg.String set_mode, 
               "<bfs(default) | dfs | dfsl | dfsh | dfshl> search strategies";
    "-debug", Arg.Set debug, " debug mode";
    "-v", Arg.Unit incr_verbose, " more debugging information";
    "-profiling", Arg.Set profiling, " profiling mode";
    "-only-forward", Arg.Set only_forward, " only do one forward search";
    "-geninv", Arg.Set gen_inv, " invariant generation";
    "-postpone", Arg.Set_int post_strategy, "<0|1|2> 0: do not postpone nodes\n                        1: postpone nodes with n+1 processes\n                        2: postpone nodes that don't add information";
    "-nodelete", Arg.Clear delete, " do not delete subsumed nodes";
    "-simpl", Arg.Set simpl_by_uc, " simplify nodes with unsat cores";
    "-j", Arg.Set_int cores, "<n> number of cores to use";
    "-dsmt", Arg.Set debug_smt, " debug mode for the SMT solver";
    "-dmcmt", Arg.Set dmcmt, " output trace in MCMT format"
  ]

let alspecs = Arg.align specs

let cin =
  let ofile = ref None in
  let set_file s =
    if Filename.check_suffix s ".cub" then ofile := Some s
    else raise (Arg.Bad "no .cub extension");
  in
  Arg.parse alspecs set_file usage;
  match !ofile with Some f -> file := f ; open_in f 
    | None -> stdin

let maxrounds = !maxrounds
let maxnodes = !maxnodes
let debug = !debug
let debug_smt = !debug_smt
let dmcmt = !dmcmt
let profiling = !profiling
let file = !file
let only_forward = !only_forward
let gen_inv = !gen_inv
let delete = !delete
let simpl_by_uc = !simpl_by_uc
let cores = !cores
let mode = if cores > 0 && !mode = Bfs then BfsDist else !mode

let post_strategy =
  if !post_strategy <> -1 then !post_strategy
  else match mode with
    | Bfs | BfsDist | Bfsinvp -> 1
    | _ -> 2

let quiet = !quiet
