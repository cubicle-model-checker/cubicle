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


val far : bool
val far_extra : string
val far_priority : string
val far_brab : bool
val far_dbg : bool
val far_verb : bool

val clusterize : bool

val int_seed : bool
val seed : int

val nb_clusters : int

val deterministic : bool
val md : int

val bwd_fwd : int

val incremental_enum : bool

val enum_steps : (int * int) list
val enum_pause : bool
val enum_verbose : bool

val filter_lvl : int
val filter_md : int

type rm = Start | End | Any

val copy_state : bool
val copy_regexp : bool
val debug_regexp : bool
val regexp_mode : rm

val res_output : bool
val res_file : string

val meta_trans : bool
val univ_trans : bool

val approx_history : bool
val hist_threshhold : int

val goods : bool

val max_proc : int
val type_only : bool
val maxrounds : int
val maxnodes : int

val only_forward : bool
val print_forward_all : bool
val print_forward_frg : bool
val gen_inv : bool
val forward_inv : int
val enumerative : int
val bmin : int
val localized : bool
val lazyinv : bool
val refine : bool
val stateless : bool
val do_brab : bool
val stop_restart : bool
val brab_up_to : bool
val murphi : bool
val murphi_uopts : string
val mu_cmd : string
val mu_opts : string
val cpp_cmd : string


(* val limit_forward_depth : bool *)
val brab_fwd_depth  : (int * int) list
val max_forward : int
val max_cands : int
val candidate_heuristic : int
val forward_sym : bool

val abstr_num : bool
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
val dot_prof : int
val bdot_prof : bool
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


val js_mode : unit -> bool


val set_js_mode : bool -> unit
