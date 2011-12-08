(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Universite Paris-Sud 11              *)
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

let incr_verbose () = incr verbose

let debug_smt = ref false
let profiling = ref false

let gen_inv = ref false
let alwayspost = ref false
let delete = ref false
let simpl_by_uc = ref false
let cores = ref 0

let mode = ref DfsHL
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
    "-type-only", Arg.Set type_only, " stop after typing";
    "-depth", Arg.Set_int maxrounds, "<nb> max depth of the search tree (default 100)";
    "-nodes", Arg.Set_int maxrounds, "<nb> max number nodes to explore (default 100000)";
    "-search", Arg.String set_mode, 
               "<dfs | dfsl | dfsh | dfshl(default) | bfs> search strategies";
    "-debug", Arg.Set debug, " debug mode";
    "-v", Arg.Unit incr_verbose, " more debugging information";
    "-profiling", Arg.Set profiling, " profiling mode";
    "-geninv", Arg.Set gen_inv, " invariant generation";
    "-alwayspost", Arg.Set alwayspost, " postpone states with n+1 processes";
    "-delete", Arg.Set delete, " delete subsumed nodes";
    "-simpl", Arg.Set simpl_by_uc, " simplify nodes with unsat cores";
    "-j", Arg.Set_int cores, "<n> number of cores to use";
    "-dsmt", Arg.Set debug_smt, " debug mode for the SMT solver"
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
let profiling = !profiling
let file = !file
let gen_inv = !gen_inv
let alwayspost = !alwayspost
let delete = !delete
let simpl_by_uc = !simpl_by_uc
let cores = !cores
let mode = if cores > 0 && !mode = Bfs then BfsDist else !mode
