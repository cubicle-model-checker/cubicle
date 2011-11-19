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

type t

type exp

val empty : t

val singleton : Solver_types.atom -> t

val union : t -> t -> t

val merge : t -> t -> t

val iter_atoms : (Solver_types.atom -> unit)  -> t -> unit

val print : Format.formatter -> t -> unit


val fresh_exp : unit -> int

val remove_fresh : int -> t -> t option

val add_fresh : int -> t -> t

val print_proof : Format.formatter -> t -> unit
