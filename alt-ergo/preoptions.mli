(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

val fmt : Format.formatter
val file : string ref

val parse_only : bool ref
val type_only : bool ref
val stopb : int ref
val stepsb : int ref
val age_limite : int ref
val notriggers : bool ref
val debug : bool ref
val debug_cc : bool ref
val debug_use : bool ref
val debug_uf : bool ref
val debug_fm : bool ref
val debug_sum : bool ref
val debug_arith : bool ref
val debug_bitv : bool ref
val debug_ac : bool ref
val debug_sat : bool ref
val debug_sat_simple : bool ref
val debug_typing : bool ref
val debug_constr : bool ref
val debug_pairs : bool ref
val debug_arrays : bool ref
val debug_combine : bool ref
val verbose : bool ref
val debug_dispatch : bool ref
val tracefile :string ref
val smtfile :bool ref
val smt2file :bool ref
val satmode : bool ref
val bjmode : bool ref
val glouton : bool ref
val triggers_var : bool ref
val redondance : int ref
val astuce : bool ref
val select : int ref
val cin : in_channel ref
val no_rm_eq_existential : bool ref
val nocontracongru : bool ref
val omega : bool ref
val arrays : bool ref
val pairs : bool ref
val term_like_pp : bool ref
val debug_types : bool ref
val all_models : bool ref
val smt_arrays : bool ref
val goal_directed : bool ref
val bouclage : int ref
val max_split : Num.num ref
val rewriting : bool ref
val proof : bool ref
val debug_proof : bool ref
val qualif : int ref
val vsid : bool ref
val debug_split : bool ref

val show_version : unit -> unit
val show_libdir : unit -> unit
val set_max_split : string -> unit
val set_proof : bool -> unit
