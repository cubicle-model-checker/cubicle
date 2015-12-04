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

val file : string
val cin : in_channel


val far : bool
val far_extra : string
val far_priority : string
val far_brab : bool

val max_proc : int
val type_only : bool
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

val limit_forward_depth : bool
val forward_depth : int
val max_forward : int
val max_cands : int
val candidate_heuristic : int

val abstr_num : bool
val num_range : int * int

val post_strategy : int
val delete : bool
val simpl_by_uc : bool
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
