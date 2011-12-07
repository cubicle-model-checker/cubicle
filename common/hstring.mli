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

open Hashcons 

module TimeHS : Timer.S

type t = string hash_consed

val make : string -> t

val view : t -> string

val equal : t -> t -> bool

val compare : t -> t -> int

val hash : t -> int

val empty : t 

val list_assoc : t -> (t * 'a) list -> 'a

val list_mem_assoc : t -> (t * 'a) list -> bool

val list_mem : t -> t list -> bool

val list_mem_couple : t * t -> (t * t) list -> bool

val compare_list : t list -> t list -> int

module H : Hashtbl.S with type key = t
