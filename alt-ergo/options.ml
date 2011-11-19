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

open Preoptions

let fmt = fmt
let file = file
let satmode = satmode
let smt2file = smt2file
let smtfile = smtfile

let cin = !cin

let type_only = !type_only
let parse_only = !parse_only
let stopb = !stopb
let stepsb = !stepsb
let age_limite = !age_limite
let notriggers = !notriggers
let debug = !debug
let debug_cc = !debug_cc
let debug_use = !debug_use
let debug_uf = !debug_uf
let debug_fm = !debug_fm
let debug_sum = !debug_sum
let debug_arith = !debug_arith
let debug_bitv = !debug_bitv
let debug_ac   = !debug_ac
let debug_sat = !debug_sat
let debug_sat_simple = !debug_sat_simple
let debug_typing = !debug_typing
let debug_constr = !debug_constr
let debug_pairs = !debug_pairs
let verbose = !verbose
let debug_dispatch = !debug_dispatch
let tracefile = !tracefile
let bjmode = !bjmode
let glouton = !glouton
let triggers_var = !triggers_var
let redondance = !redondance
let astuce = !astuce
let select = !select
let no_rm_eq_existential = !no_rm_eq_existential
let nocontracongru = !nocontracongru
let omega = !omega
let arrays = !arrays
let pairs = !pairs
let term_like_pp = !term_like_pp
let debug_arrays = !debug_arrays
let debug_types = !debug_types
let all_models = !all_models
let debug_combine = !debug_combine
let smt_arrays = ! smt_arrays
let goal_directed = !goal_directed
let bouclage = ! bouclage
let max_split = !max_split
let rewriting = !rewriting
let proof = !proof
let debug_proof = !debug_proof && proof
let qualif = !qualif
let vsid = !vsid
let debug_split = !debug_split
