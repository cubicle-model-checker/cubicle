(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

type trace =  NoTrace | AltErgoTr | WhyTr | WhyInst

type viz_prog = Dot | Sfdp

type solver = AltErgo | Z3

let js_mode = ref false

let usage = "usage: cubicle file.cub"
let file = ref "_stdin"

let parse_only = ref false

let max_proc = ref 10
let type_only = ref false
let maxrounds = ref 100
let maxnodes = ref 100_000
let debug = ref false
let dot = ref false
let dot_level = ref 0
let dot_prog = ref Dot
let dot_colors = ref 0
let verbose = ref 0
let quiet = ref false
let bitsolver = ref false
let enumsolver = ref false

let unDepth = ref 1
let interpretProcs = ref 3
let debug_interpreter = ref false
let interpreter = ref false 
let int_brab = ref (-1)
let depth_ib = ref (-1)
let rounds = ref (-1)
let mrkv_brab = ref 0
let int_brab_quiet = ref false
let int_deadlock = ref false
  
let incr_verbose () = incr verbose

let debug_smt = ref false
let dmcmt = ref false
let profiling = ref false
let nocolor = ref false

let only_forward = ref false
let gen_inv = ref false
let forward_inv = ref (-1)
let enumerative = ref (-1)
let murphi = ref false
let murphi_uopts = ref ""
let mu_cmd = ref "mu"
let mu_opts = ref ""
let cpp_cmd = ref "g++ -O4"

let brab = ref (-1)
let brab_up_to = ref false
let forward_depth = ref (-1)
let localized = ref false 
let lazyinv = ref false
let refine = ref false
let stateless = ref false
let max_cands = ref (-1)
let max_forward = ref (-1)
let candidate_heuristic = ref (-1)
let forward_sym = ref true

let abstr_num = ref false
let num_range_low = ref 0
let num_range_up = ref 0

let post_strategy = ref (-1)
let delete = ref true
let simpl_by_uc = ref false
let cores = ref 0
let refine_universal = ref false

let subtyping = ref true
let notyping = ref false
let noqe = ref false

let trace = ref NoTrace
let set_trace = function
  | "alt-ergo" -> trace := AltErgoTr
  | "why" | "why3" -> trace := WhyTr
  | "whyinst" | "why3inst" -> trace := WhyInst
  | _ -> raise (Arg.Bad "Proof format = alt-ergo | why3 | why3inst")

let out = ref "."
let set_out o =
  if not (Sys.file_exists o) then Unix.mkdir o 0o755
  else if not (Sys.is_directory o) then
    raise (Arg.Bad "-out takes a directory as argument");
  out := o

let mode = ref "bfs"
let set_mode m =
  mode := m;
  match m with
  | "bfs" | "bfsh" | "bfsa" | "dfs" | "dfsh" | "dfsa" -> ()
  | _ -> raise (Arg.Bad ("search strategy "^m^" not supported"))

let smt_solver = ref AltErgo
let set_smt_solver s =
  smt_solver := match s with
    | "alt-ergo" -> AltErgo
    | "z3" -> Z3
    | _ -> raise (Arg.Bad ("SMT solver "^s^" not supported"))

let set_dot d =
  dot := true;
  dot_level := d

let use_sfdp () =
  dot_prog := Sfdp

let show_version () = Format.printf "%s@." Version.version; exit 0

let specs = 
  [ "-version", Arg.Unit show_version, " prints the version number";
    "-quiet", Arg.Set quiet, " do not output search trace";
    "-nocolor", Arg.Set nocolor, " disable colors in ouptut";
    "-type-only", Arg.Set type_only, " stop after typing";
    "-parse-only", Arg.Set parse_only, " stop after parsing";
    "-max-procs", Arg.Set_int max_proc, 
    "<nb> max number of processes to introduce (default 10)";
    "-depth", Arg.Set_int maxrounds, 
    "<nb> max depth of the search tree (default 100)";
    "-nodes", Arg.Set_int maxnodes, 
    "<nb> max number nodes to explore (default 100000)";
    "-search", Arg.String set_mode, 
    "<bfs(default) | bfsh | bfsa | dfs | dfsh | dfsa> search strategies";
    "-debug", Arg.Set debug, " debug mode";
    "-dot", Arg.Int set_dot,
    "<level> graphviz (dot) output with a level of details";
    "-sfdp", Arg.Unit use_sfdp,
    " use sfdp for drawing graph instead of dot (for big graphs)";
    "-dot-colors", Arg.Set_int dot_colors,
    "number of colors for dot output";
    "-v", Arg.Unit incr_verbose, " more debugging information";
    "-profiling", Arg.Set profiling, " profiling mode";
    "-only-forward", Arg.Set only_forward, " only do one forward search";
    "-geninv", Arg.Set gen_inv, " invariant generation";
    "-symbolic", Arg.Set_int forward_inv, 
    "<n> symbolic forward invariant generation with n processes";
    "-enumerative", Arg.Set_int enumerative, 
    "<n> enumerative forward invariant generation with n processes";
    "-local", Arg.Set localized, 
    " localized invariant candidates";
    "-brab", Arg.Set_int brab,
    "<nb> Backward reachability with approximations and backtrack helped \
     with a finite model of size <nb>";
    "-int-brab", Arg.Tuple [ Arg.Set_int int_brab;
			     Arg.Set_int rounds;
			     Arg.Set_int depth_ib;
			     Arg.Set_int mrkv_brab], " <nb> procs <nb> rounds <nb> depth <bool> smart";
    "-int-brab-debug", Arg.Set int_brab_quiet, " Activate interpreter brab";
    "-int-deadlock", Arg.Set int_deadlock, " Deadlock details for interpreter forward";
    "-upto", Arg.Set brab_up_to,
    " in combination with -brab <n>, finite models up to size <n>";
    "-murphi", Arg.Set murphi,
    " use Murphi for enumerative forward instead of the naive implementation";
    "-murphi-opt", Arg.Set_string murphi_uopts,
    " options passed to Murphi (as is)";
    "-mu", Arg.Set_string mu_cmd, "Murphi compiler command line (default: mu)";
    "-mu-opt", Arg.Set_string mu_opts,
    " Murphi compiler options (passed as is, no options by default)";
    "-cpp", Arg.Set_string cpp_cmd, " C++ compiler command line (default: g++ -O4)";
    "-forward-depth", Arg.Set_int forward_depth,
    "<d> Limit the depth of the forward exploration to at most d";
    "-max-forward", Arg.Set_int max_forward,
    "<d> Limit the number of states of the forward exploration to at most d";
    "-max-cands", Arg.Set_int max_cands,
    "<d> Limit the number of candidates considered for approximations to \
     at most d";
    "-candheur", Arg.Set_int candidate_heuristic,
    "<d> set the heuristic used for generating candidate invariants \
     (size measure d)";
    "-abstr-num", Arg.Tuple [Arg.Set_int num_range_low;
                             Arg.Set_int num_range_up;
                             Arg.Set abstr_num],
    "<low> <up> abstract numerical values in [<low>; <up>] during forward \
     exploration";
    "-stateless", Arg.Set stateless, " stateless symbolic forward search";
    "-forward-nosym", Arg.Clear forward_sym,
    " disable symmetry reduction in forward exploration";
    "-postpone", Arg.Set_int post_strategy, 
    "<0|1|2> 
                          0: do not postpone nodes
                          1: postpone nodes with n+1 processes
                          2: postpone nodes that don't add information";
    "-nodelete", Arg.Clear delete, " do not delete subsumed nodes";
    "-nosubtyping", Arg.Clear subtyping, " no static subtyping analysis";
    "-simpl", Arg.Set simpl_by_uc, " simplify nodes with unsat cores";
    "-noqe", Arg.Set noqe, " disable elimination of postivie constants";
    "-refine-universal", Arg.Set refine_universal,
    " refine universal guards by symbolic forward";
    "-j", Arg.Set_int cores, "<n> number of cores to use";
    "-solver", Arg.String set_smt_solver,
    "<alt-ergo(default) | z3> SMT solver to use";
    "-dsmt", Arg.Set debug_smt, " debug mode for the SMT solver";
    "-dmcmt", Arg.Set dmcmt, " output trace in MCMT format";
    "-bitsolver", Arg.Set bitsolver, " use bitvector solver for finite types";
    "-enumsolver", Arg.Set enumsolver,
    " use Enumerated data types solver for finite types";
    "-trace", Arg.String set_trace, " <alt-ergo | why> search strategies";
    "-out", Arg.String set_out,
    "<dir> set output directory for certificate traces to <dir>";
    (* Hidden options *)
    "-notyping", Arg.Set notyping, " disable typing"; (* Disable typing *)
    "-undepth", Arg.Set_int unDepth, " depth of unsafe";
    "-interpret-proc", Arg.Set_int interpretProcs, " how many procs for interpreter";
    "-interpreter", Arg.Set interpreter, " start interpreter";
    "-debug-interpret", Arg.Set debug_interpreter, " debug interpreter";
  ]

let alspecs = Arg.align specs

let cin =
  let ofile = ref None in
  let set_file s =
    if Filename.check_suffix s ".cub" then ofile := Some s
    else raise (Arg.Bad "no .cub extension");
  in
  Arg.parse alspecs set_file usage;
  match !ofile with 
  | Some f -> file := f ; open_in f 
  | None -> stdin


let int_brab = !int_brab
let depth_ib = !depth_ib
let rounds = !rounds
let mrkv_brab = !mrkv_brab
let int_brab_quiet = !int_brab_quiet

    

let parse_only = !parse_only 
let type_only = !type_only
let maxrounds = !maxrounds
let maxnodes = !maxnodes
let max_proc = !max_proc
let debug = !debug
let nocolor = !nocolor
let dot = !dot
let dot_level = !dot_level
let dot_colors = !dot_colors
let dot_prog = !dot_prog
let debug_smt = !debug_smt
let dmcmt = !dmcmt
let profiling = !profiling
let file = !file
let only_forward = !only_forward
let gen_inv = !gen_inv
let forward_inv = !forward_inv
let brab = !brab
let enumerative =
  if brab <> -1 then brab
  else if int_brab <> -1 then int_brab
  else !enumerative
let do_brab = brab <> -1
let brab_up_to =
  if !brab_up_to && not do_brab then
    raise (Arg.Bad "use -upto in combination with brab")
  else !brab_up_to
let murphi = !murphi
let murphi_uopts = !murphi_uopts
let mu_cmd = !mu_cmd
let mu_opts = !mu_opts
let cpp_cmd = !cpp_cmd

let max_cands = !max_cands
let max_forward = !max_forward
let candidate_heuristic =
  if !candidate_heuristic <> -1 then !candidate_heuristic else enumerative
let forward_depth = !forward_depth
let limit_forward_depth = forward_depth <> -1
let forward_sym = !forward_sym
let localized = !localized
let refine = !refine && not !stateless
let lazyinv = !lazyinv
let stateless = !stateless
let delete = !delete
let simpl_by_uc = !simpl_by_uc
let noqe = !noqe

let cores = !cores


  

let unDepth = !unDepth
let interpreter = !interpreter
let debug_interpreter = !debug_interpreter
let int_deadlock = !int_deadlock




let mode = !mode
let smt_solver = !smt_solver

let verbose = !verbose

let post_strategy =
  if !post_strategy <> -1 then !post_strategy
  else match mode with
    | "bfs" | "bfsa" -> 1
    | "bfsh" | "dfsh" -> 0
    | "dfs" | "dfsa" -> 2
    | _ -> 1

let abstr_num = !abstr_num
let num_range = (!num_range_low, !num_range_up)

let quiet = !quiet
let bitsolver = !bitsolver
let enumsolver = !enumsolver

let size_proc = ref 0

let refine_universal = !refine_universal

let subtyping =
  if !trace = NoTrace then !subtyping
  else
    begin
      if not quiet then
        Format.printf "Deactivating subtyping analysis for traces.@.";
      false
    end

let notyping = !notyping

let trace = !trace
let out_trace = !out



(* Setters *)
let set_js_mode b = js_mode := b


(* Getters *)
let js_mode () = !js_mode


let set_interpret_procs n = interpretProcs := n
let get_interpret_procs () = !interpretProcs
