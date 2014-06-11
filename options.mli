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

type trace =  NoTrace | AltErgoTr | WhyTr

type value = 
  | VVar of Hstring.t
  | Numb of Num.num
  | Hstr of Hstring.t 
  | Proc of int

val file : string
val cin : in_channel

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

val abstr_num : bool
val num_range : int * int

val post_strategy : int
val delete : bool
val simpl_by_uc : bool
val bitsolver : bool
val enumsolver : bool
val refine_universal : bool

val cores : int

val mode : mode

val debug : bool
val dot : bool
val quiet : bool
val verbose : int
val nocolor : bool

val debug_smt : bool
val dmcmt : bool
val profiling : bool

val size_proc : int ref

val subtyping : bool

val trace : trace
val out_trace : string

val nb_threads : int
val upd : int
val fproc : value
val nb_exec : int
val schedule : bool
val runs : int
val bequit : bool
val compare : bool
val tab_init : (Hstring.t, (value * int) list) Hashtbl.t
val proc_init : (Hstring.t, value list) Hashtbl.t
val proc_ninit : (Hstring.t, unit) Hashtbl.t

(* val tab_init : (int * Hstring.t list) Hashtbl.t *)

val ofile : string option
val init_proc : bool ref
