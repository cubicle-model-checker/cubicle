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

type mode = Dfs | DfsL | DfsH | DfsHL | Bfs 

let usage = "usage: backward file.cub"
let file = ref " stdin"

let type_only = ref false
let maxrounds = ref 60
let debug = ref false
let verbose = ref 0

let incr_verbose () = incr verbose

let debug_altergo = ref false
let profiling = ref false

let gen_inv = ref false

let mode = ref Dfs
let set_mode = function
  | "dfs" -> mode := Dfs
  | "dfsl" -> mode := DfsL
  | "dfsh" -> mode := DfsH
  | "dfshl" -> mode := DfsHL
  | "bfs" -> mode := Bfs
  | _ -> raise (Arg.Bad "search strategy not supported")

let show_version () = Format.printf "%s@." Version.version; exit 0

let specs = 
  [ "-version", Arg.Unit show_version, "  prints the version number";
    "-type-only", Arg.Set type_only, " stop after typing";
    "-rounds", Arg.Set_int maxrounds, " max number of rounds";
    "-search", Arg.String set_mode, 
               " <dfs(default) | dfsg | dfsh | dfshg | bfs> search strategies";
    "-debug", Arg.Set debug, " debug mode";
    "-v", Arg.Unit incr_verbose, " mode debugging information";
    "-profiling", Arg.Set profiling, " profiling mode";
    "-geninv", Arg.Set gen_inv, " invariant generation";
    "-dergo", Arg.Set debug_altergo, " debug mode for alt-ergo"
  ]

let cin =
  let ofile = ref None in
  let set_file s =
    if Filename.check_suffix s ".cub" then ofile := Some s
    else raise (Arg.Bad "no .cub extension");
  in
  Arg.parse specs set_file usage;
  match !ofile with Some f -> file := f ; open_in f 
    | None -> stdin

let maxrounds = !maxrounds
let debug = !debug
let debug_altergo = !debug_altergo
let profiling = !profiling
let file = !file
let gen_inv = !gen_inv
