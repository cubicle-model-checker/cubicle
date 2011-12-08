(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)


exception AlreadyDeclared of Hstring.t
exception Undefined of Hstring.t

(* API for the construction of types, terms and formulas *)

module Typing : sig
  type t

  val type_int : Hstring.t
  val type_bool : Hstring.t
  val type_proc : Hstring.t
    
  val declare_type : Hstring.t * Hstring.t list -> unit
  val declare_name : Hstring.t -> Hstring.t list -> Hstring.t -> unit

  val find : Hstring.t -> Hstring.t list * Hstring.t
end

module Term : sig
  type t
  type operator = Plus | Minus | Mult | Div | Modulo

  val make_int : int -> t
  val make_app : Hstring.t -> t list -> t
  val make_arith : operator -> t -> t -> t
end

module Formula : sig
  type t
  type comparator = Eq | Neq | Le | Lt
  type combinator = And | Or | Imp | Not

  val vrai : t
  val faux : t

  val make_lit : comparator -> Term.t list -> t
  val make : combinator -> t list -> t
  val print : Format.formatter -> t -> unit
end

(* SMT solver interface *)

exception Sat 
exception Unsat of Explanation.t 
exception IDontknow

val get_time : unit -> float
val get_calls : unit -> int

val clear : unit -> unit
val assume : Formula.t -> unit
val check : profiling:bool -> unit


