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

(** Options given on the command line  *)

type trace =  NoTrace | AltErgoTr | WhyTr | WhyInst

type viz_prog = Dot | Sfdp

type solver = AltErgo | Z3

val file : string
val cin : in_channel

val max_proc : int
val type_only : bool
val parse_only: bool

val maxrounds : int
val maxnodes : int

val only_forward : bool
val gen_inv : bool
val forward_inv : int
val enumerative : int
val localized : bool
val lazyinv : bool
val refine : bool
val stateless : bool
val do_brab : bool
val brab_up_to : bool
val murphi : bool
val murphi_uopts : string
val mu_cmd : string
val mu_opts : string
val cpp_cmd : string


val limit_forward_depth : bool
val forward_depth : int
val max_forward : int
val max_cands : int
val candidate_heuristic : int
val forward_sym : bool

val abstr_num : bool
val num_range_up : int
val num_range : int * int

val post_strategy : int
val delete : bool
val simpl_by_uc : bool
val noqe : bool
val bitsolver : bool
val enumsolver : bool
val refine_universal : bool

val cores : int

val mode : string

val debug : bool
val dot : bool
val dot_level : int
val dot_prog : viz_prog
val dot_colors : int
val quiet : bool
val verbose : int
val nocolor : bool

val smt_solver : solver
val debug_smt : bool
val dmcmt : bool
val profiling : bool

val size_proc : int ref

val subtyping : bool
val notyping : bool

val trace : trace
val out_trace : string

val unDepth : int
val interpreter : bool
val fuzz : bool
val debug_interpreter : bool
val depth_ib : int
val rounds : int
val mrkv_brab : int
val int_brab_quiet : bool
val int_deadlock : bool 

val fuzz_s : int
val fuzz_d : int
val fuzz_t : int

val fuzz_bench : float
val fuzz_bench_time : bool
val bench : bool
val bench_rand : bool


val js_mode : unit -> bool


val set_js_mode : bool -> unit


val set_interpret_procs : int -> unit
val get_interpret_procs : unit -> int

  
val set_int_brab : int -> unit
val get_int_brab : unit -> int

val set_num_range_low : int -> unit
val set_num_range_up : int -> unit
val get_num_range_up : unit -> int
val get_num_range_low : unit -> int


val get_num_range : unit -> int * int
