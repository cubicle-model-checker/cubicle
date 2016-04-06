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

(* FAR *)

let far = ref false
let far_extra = ref "no"
let far_priority = ref "bfs"
let far_brab = ref false
let far_dbg = ref false
let far_verb = ref false

(* CLUSTERING *)

let clusterize = ref false

let nb_clusters = ref (-1)

let deterministic = ref false
let md = ref 0

let filter_lvl = ref 0
let filter_md = ref 0

let int_seed = ref false
let seed = ref 0

(* INCREMENTAL ENUMERATIVE WITH CLUSTERING *)

let incremental_enum = ref false

let frg = ref (-1)
let enum_steps = ref []
let enum_pause = ref false
let enum_verbose = ref false

(* STATE COPY *)
let copy_state = ref false
let copy_regexp = ref false
let debug_regexp = ref false

type rm = Start | End | Any

let regexp_mode = ref Start

let set_debug_regexp s = 
  (match s with 
    | "start" -> regexp_mode := Start
    | "end" -> regexp_mode := End
    | "any" -> regexp_mode := Any
    | _ -> raise (Arg.Bad "Regexp mode = start | end | any"));
  debug_regexp := true

let res_output = ref false
let res_file = ref ""

let meta_trans = ref false
let univ_trans = ref false

let set_res_output s =
  res_output := true;
  res_file := s

(* BWD *)

let bwd_fwd = ref (-1)

let goods = ref false

let max_proc = ref 10
let type_only = ref false
let maxrounds = ref 100
let maxnodes = ref 100_000
let debug = ref false
let dot = ref false
let dot_level = ref 0
let dot_prof = ref 0
let dot_prog = ref Dot
let dot_colors = ref 0
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
let print_forward_all = ref false
let print_forward_frg = ref false
let gen_inv = ref false
let forward_inv = ref (-1)
let enumerative = ref (-1)
let murphi = ref false
let murphi_uopts = ref ""
let mu_cmd = ref "mu"
let mu_opts = ref ""
let cpp_cmd = ref "g++ -O4"

let brab = ref []
let stop_restart = ref false
let bmin = ref (-1)
let brab_up_to = ref false
let forward_depth = ref []
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

let set_far n =
  far := true;
  match n with
    | "no" | "basic" | "fwd" -> far_extra := n
    | "fwd-brab" -> far_extra := n; far_brab := true
    | _ -> raise (Arg.Bad ("extrapolation strategy "^n^" not supported"))

let set_seed n =
  int_seed := true;
  seed := n

let set_deterministic n =
  deterministic := true;
  md := n

let set_ienum () =
  deterministic := true;
  incremental_enum := true

let set_partial_frg k = enum_steps := (!frg, k) :: !enum_steps

let set_brab_nol b = brab := (b, -1) :: !brab
let tmp_brab = ref (-1)
let set_brab_lim f = brab := (!tmp_brab, f) :: !brab

let set_fwd_depth f = match !brab with
  | (b, _) :: tl -> brab := (b, f) :: tl
  | [] -> raise (Arg.Bad ("You should set a brab value before giving it a\
                           max depth"))

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
    "-fverb", Arg.Set far_verb, " output search trace for far";
    "-nocolor", Arg.Set nocolor, " disable colors in ouptut";
    "-type-only", Arg.Set type_only, " stop after typing";
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
    "-dot-prof", Arg.Set_int dot_prof,
              "<prof> set the maximum depth of a displayable node";
    "-sfdp", Arg.Unit use_sfdp,
    " use sfdp for drawing graph instead of dot (for big graphs)";
    "-dot-colors", Arg.Set_int dot_colors,
    "number of colors for dot output";
    "-v", Arg.Unit incr_verbose, " more debugging information";
    "-profiling", Arg.Set profiling, " profiling mode";
    "-res", Arg.String set_res_output, " output forward and bwd informations in file";
    "-only-forward", Arg.Set only_forward, " only do one forward search";
    "-of", Arg.Set only_forward, " only do one forward search";
    "-pall", Arg.Set print_forward_all, " print forwarded states";
    "-pfrg", Arg.Set print_forward_frg, " print forwarded states";
    "-cluster", Arg.Set clusterize, " clusterize the last visited nodes";
    "-seed", Arg.Int set_seed , "<n> seed for rng";
    "-k", Arg.Set_int nb_clusters, "<n> number of clusters (if random initialization)";
    "-det", Arg.Int set_deterministic, 
    "<n> deterministic method to find k with a <n> being the max distance";
    "-ie", Arg.Unit set_ienum, " incremental enumerative with fringes clustering";
    "-iep", Arg.Set enum_pause, " pause between clusterings (for debug, only)";
    "-iev", Arg.Set enum_verbose, " debugging informations";
    "-cfd", Arg.Tuple ([Arg.Set_int frg; Arg.Int set_partial_frg]), 
    "<n m> clusterize fringe at prof <n> with <m> being the max distance\
       before going on with enumerative";
    "-copy", Arg.Set copy_state, " copy states that look general enough";
    "-creg", Arg.Set copy_regexp, " copy states that have a recognized history";
    "-dreg", Arg.String set_debug_regexp, 
    "<start(default) | end | any> debugging regexps to know if a path has been taken";
    "-meta", Arg.Set meta_trans, " use meta transitions for forward and backward";
    "-univ", Arg.Set univ_trans, 
    " use universal transitions for forward and backward";
    "-bstop", Arg.Set stop_restart, " exit the program at first restart";
    "-flvl", Arg.Set_int filter_lvl, "<n> set a filtering level to clusters";
    "-md", Arg.Set_int filter_md, 
    "<n> set a minimum distance inside a cluster for filtering";
    "-bwd", Arg.Set_int bwd_fwd, 
    "<n> do a non approximate backward to prof <n> to help the oracle";
    "-geninv", Arg.Set gen_inv, " invariant generation";
    "-symbolic", Arg.Set_int forward_inv, 
    "<n> symbolic forward invariant generation with n processes";
    "-enumerative", Arg.Set_int enumerative, 
    "<n> enumerative forward invariant generation with n processes";
    "-local", Arg.Set localized, 
    " localized invariant candidates";
    "-far-extra", Arg.String set_far, 
                "<no(default) | basic | fwd | fwd-brab> use far with strategy <n> of abstraction";
    "-far-dbg", Arg.Set far_dbg, " Provisoire";
    "-goods", Arg.Set goods, " Goods";
    "-brab", Arg.Int set_brab_nol,
    "<nb> Backward reachability with approximations and backtrack helped \
     with a finite model of size <nb>";
    "-brabfd", Arg.Tuple [Arg.Set_int tmp_brab;
                          Arg.Int set_brab_lim],
    "<nb> Backward reachability with fd with approximations and backtrack helped \
     with a finite model of size <nb>";
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
    "-forward-depth", Arg.Int set_fwd_depth,
    "<d> Limit the depth of the forward exploration to at most d";
    "-fd", Arg.Int set_fwd_depth,
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
    "-fnos", Arg.Clear forward_sym,
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
    "-dsmt", Arg.Set debug_smt, " debug mode for the SMT solver";
    "-dmcmt", Arg.Set dmcmt, " output trace in MCMT format";
    "-bitsolver", Arg.Set bitsolver, " use bitvector solver for finite types";
    "-enumsolver", Arg.Set enumsolver,
    " use Enumerated data types solver for finite types";
    "-trace", Arg.String set_trace, "<alt-ergo | why> search strategies";
    "-out", Arg.String set_out,
    "<dir> set output directory for certificate traces to <dir>";
    (* Hidden options *)
    "-notyping", Arg.Set notyping, ""; (* Disable typing *)
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

let far = !far
let far_extra = 
  match !far_extra with
    | "oracle" | "fwd" | "fwd-brab" as f -> 
      if !brab = [] then raise 
        (Arg.Bad "You should give a number of processes to brab")
      else f
    | f -> f

let far_priority = !far_priority
  
let far_brab = !far_brab
let far_dbg = !far_dbg
let far_verb = !far_verb

let clusterize = !clusterize


let nb_clusters = !nb_clusters

let int_seed = !int_seed
let seed = !seed

let deterministic = !deterministic

let () =
  if clusterize && not deterministic && nb_clusters = -1 then
    raise (Arg.Bad "You should give a number of clusters when randomly initializing")

let md = !md

let enum_steps =  
  List.sort (fun (f, _) (f', _) -> Pervasives.compare f f') !enum_steps
    
let incremental_enum = 
  let ie = !incremental_enum in
  if ie && enum_steps = [] then
    raise (Arg.Bad "You should determine steps to clusterize when using\
                    incremental enumerative");
  ie

let filter_lvl = !filter_lvl
let filter_md = !filter_md
let enum_pause = !enum_pause
let enum_verbose = !enum_verbose

let copy_state = !copy_state
let copy_regexp = !copy_regexp
let regexp_mode = !regexp_mode
let debug_regexp = !debug_regexp

let res_output = !res_output
let res_file = !res_file

let meta_trans = !meta_trans
let univ_trans = !univ_trans

let bwd_fwd = !bwd_fwd

let goods = !goods

let type_only = !type_only
let maxrounds = !maxrounds
let maxnodes = !maxnodes
let max_proc = !max_proc
let debug = !debug
let nocolor = !nocolor
let dot = !dot
let dot_level = !dot_level
let dot_prof = !dot_prof
let bdot_prof = dot_prof > 0
let dot_colors = !dot_colors
let dot_prog = !dot_prog
let debug_smt = !debug_smt
let dmcmt = !dmcmt
let profiling = !profiling
let file = !file
let only_forward = !only_forward
let print_forward_all = !print_forward_all
let print_forward_frg = !print_forward_frg
let gen_inv = !gen_inv
let forward_inv = !forward_inv
let brab = List.rev !brab
let stop_restart = !stop_restart
let bmin = !bmin
let max_brab = List.fold_left (fun m (e, _) -> max e m) (-1) brab
let enumerative = if brab <> [] then max_brab else !enumerative
let do_brab = brab <> []
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

let forward_depth = List.rev !forward_depth

let brab_fwd_depth = brab

let limit_forward_depth = forward_depth <> []
let forward_sym = !forward_sym
let localized = !localized
let refine = !refine && not !stateless
let lazyinv = !lazyinv
let stateless = !stateless
let delete = !delete
let simpl_by_uc = !simpl_by_uc
let noqe = !noqe


let cores = !cores

let mode = !mode

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

let smt_solver = !smt_solver
