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

(*let fmt = Format.std_formatter*)
let fmt = Format.err_formatter

let file = ref " stdin"
let cin = ref stdin

let bouclage = ref 1
let smt_arrays = ref false
let rewriting = ref false
let type_only = ref false
let parse_only = ref false
let stopb = ref 8
let stepsb = ref (-1)
let age_limite = ref 10
let debug = ref false
let notriggers = ref false
let debug_cc = ref false
let debug_use = ref false
let debug_arrays = ref false
let debug_uf = ref false
let debug_sat = ref false
let debug_sat_simple = ref false
let debug_typing = ref false
let debug_constr = ref false
let debug_pairs = ref false
let verbose = ref false
let debug_fm = ref false
let debug_sum = ref false
let debug_arith = ref false
let debug_combine = ref false
let debug_bitv = ref false
let debug_ac = ref false
let debug_dispatch = ref false
let debug_split = ref false
let options = ref false
let tracefile = ref ""
let smtfile = ref false
let smt2file = ref false
let satmode = ref false
let bjmode = ref false
let glouton = ref false
let triggers_var = ref false
let redondance = ref 4
let astuce = ref false
let select = ref 0
let no_rm_eq_existential = ref false
let nocontracongru = ref false
let omega = ref false
let arrays = ref false
let pairs = ref false
let term_like_pp = ref true
let debug_types = ref false 
let all_models = ref false
let goal_directed = ref false
let proof = ref false
let debug_proof = ref false
let qualif = ref (-1)
let vsid = ref false
let max_split = ref (Num.Int 1000000)

let show_version () = Format.printf "%s@." Version.version; exit 0
let show_libdir () = Format.printf "%s@." Version.libdir; exit 0

let set_max_split s = max_split := Num.num_of_string s

let set_proof b = proof := b
