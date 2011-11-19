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

val ale : Hstring.t (* <= *)
val alt : Hstring.t (* < *)
val agt : Hstring.t (* > *)

val is_le : Hstring.t -> bool
val is_lt : Hstring.t -> bool
val is_gt : Hstring.t -> bool
val is_builtin : string -> Hstring.t
