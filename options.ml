(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

type mode = 
  | Dfs | DfsL | DfsH | DfsHL 
  | Bfs | BfsDist | Bfsinvp 
  | Induct

let usage = "usage: cubicle file.cub"
let file = ref " stdin"

let max_proc = 10
let type_only = ref false
let maxrounds = ref 100
let maxnodes = ref 100_000
let debug = ref false
let dot = ref false
let verbose = ref 0
let quiet = ref false
let bitsolver = ref false
let enumsolver = ref false

let incr_verbose () = incr verbose

let debug_smt = ref false
let dmcmt = ref false
let profiling = ref false
let nocolor = ref false

let only_forward = ref false
let gen_inv = ref false
let forward_inv = ref (-1)
let enumerative = ref (-1)
let brab = ref (-1)
let localized = ref false 
let lazyinv = ref false
let refine = ref false
let stateless = ref false

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
  | "induct" -> mode := Induct
  | _ -> raise (Arg.Bad "search strategy not supported")

let show_version () = Format.printf "%s@." Version.version; exit 0

let specs = 
  [ "-version", Arg.Unit show_version, " prints the version number";
    "-quiet", Arg.Set quiet, " do not output search trace";
    "-nocolor", Arg.Set nocolor, " disable colors in ouptut";
    "-type-only", Arg.Set type_only, " stop after typing";
    "-depth", Arg.Set_int maxrounds, 
              "<nb> max depth of the search tree (default 100)";
    "-nodes", Arg.Set_int maxnodes, 
              "<nb> max number nodes to explore (default 100000)";
    "-search", Arg.String set_mode, 
               "<bfs(default) | dfs | dfsl | dfsh | dfshl | induct> 
               search strategies";
    "-debug", Arg.Set debug, " debug mode";
    "-dot", Arg.Set dot, " graphviz (dot) output";
    "-v", Arg.Unit incr_verbose, " more debugging information";
    "-profiling", Arg.Set profiling, " profiling mode";
    "-only-forward", Arg.Set only_forward, " only do one forward search";
    "-geninv", Arg.Set gen_inv, " invariant generation";
    "-symbolic", Arg.Set_int forward_inv, 
                    "<n> symbolic forward invariant generation with n processes";
    "-enumerative", Arg.Set_int enumerative, 
                    "<n> enumerative forward invariant generation with n processes";
    "-local", Arg.Set localized, 
                    "localized invariant candidates";
    "-brab", Arg.Set_int brab,
                "<nb> Backward reachability with approximations and backtrack helped with a finite model of size <nb>";
    "-stateless", Arg.Set stateless, " stateless symbolic forward search";
    "-postpone", Arg.Set_int post_strategy, 
                 "<0|1|2> 
                          0: do not postpone nodes
                          1: postpone nodes with n+1 processes
                          2: postpone nodes that don't add information";
    "-nodelete", Arg.Clear delete, " do not delete subsumed nodes";
    "-simpl", Arg.Set simpl_by_uc, " simplify nodes with unsat cores";
    "-j", Arg.Set_int cores, "<n> number of cores to use";
    "-dsmt", Arg.Set debug_smt, " debug mode for the SMT solver";
    "-dmcmt", Arg.Set dmcmt, " output trace in MCMT format";
    "-bitsolver", Arg.Set bitsolver, " use bitvector solver for finite types";
    "-enumsolver", Arg.Set enumsolver, " use Enumerated data types solver for finite types"
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

let type_only = !type_only
let maxrounds = !maxrounds
let maxnodes = !maxnodes
let debug = !debug
let nocolor = !nocolor
let dot = !dot
let debug_smt = !debug_smt
let dmcmt = !dmcmt
let profiling = !profiling
let file = !file
let only_forward = !only_forward
let gen_inv = !gen_inv
let forward_inv = !forward_inv
let brab = !brab
let enumerative = if brab <> -1 then brab else !enumerative
let do_brab = if brab <> -1 then true else false
let localized = !localized
let refine = !refine && not !stateless
let lazyinv = !lazyinv
let stateless = !stateless
let delete = !delete
let simpl_by_uc = !simpl_by_uc
let cores = 
  if !cores > 0 && do_brab then begin
    Format.eprintf "Error: parallel BRAB not implemented";
    exit 1;
  end
  else !cores
let mode = if cores > 0 && !mode = Bfs then BfsDist else !mode
let verbose = !verbose
let post_strategy =
  if !post_strategy <> -1 then !post_strategy
  else match mode with
    | Bfs | BfsDist | Bfsinvp -> 1
    | _ -> 2

let quiet = !quiet
let bitsolver = !bitsolver
let enumsolver = !enumsolver

