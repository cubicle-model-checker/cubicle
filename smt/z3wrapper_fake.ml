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

type error = 
  | DuplicateTypeName of Hstring.t
  | DuplicateSymb of Hstring.t
  | UnknownType of Hstring.t
  | UnknownSymb of Hstring.t

exception Error of error

let unsupported _ =
  failwith "Cubicle was not compile with the Z3 library."

let hfake = Hstring.make "fake_Z3"

module Type = struct
  type t = Hstring.t
  let equal _ _ = unsupported ()
  let type_int = hfake
  let type_real = hfake
  let type_bool = hfake
  let type_proc = hfake
  let declare _ _ = unsupported ()
  let all_constructors _ = unsupported ()
  let constructors _ = unsupported ()
end

module Symbol = struct
  type t = Hstring.t
  let declare _ _ _ = unsupported ()
  let type_of _ = unsupported ()
  let declared _ = unsupported ()
  let has_abstract_type s = unsupported ()
  let has_infinite_type s = unsupported ()
  let has_type_proc s = unsupported ()
end


module Variant = struct
  let assign_constr _ = unsupported ()
  let assign_var _ _ = unsupported ()
  let print _ = unsupported ()
  let init _ = unsupported ()
  let close _ = unsupported ()
  let get_variants _ = unsupported ()
end
  
module Term = struct
  type t = unit
  type operator = Plus | Minus | Mult | Div | Modulo
  let make_int _ = unsupported ()
  let make_real _ = unsupported ()
  let make_app _ _ = unsupported ()
  let t_true = ()
  let t_false = ()
  let make_arith _ _ _ = unsupported ()
  let is_int _ = unsupported ()
  let is_real = unsupported ()
end

module Formula = struct

  type comparator = Eq | Neq | Le | Lt
  type combinator = And | Or | Imp | Not
  type literal = unit
  type t = unit
  let print _ _ = unsupported ()
  let f_true = ()
  let f_false = ()
  let make_lit _ _ = unsupported ()
  let make _ _ = unsupported ()
  let make_cnf _ = unsupported ()
end

exception Unsat of int list

let set_cc _ = unsupported ()
let set_arith _ = unsupported ()
let set_sum _ = unsupported ()

module type Solver = sig
  type state

  val get_time : unit -> float
  val get_calls : unit -> int

  val clear : unit -> unit
  val assume : id:int -> Formula.t -> unit
  val check : unit -> unit

  val save_state : unit -> state
  val restore_state : state -> unit
  val entails : id:int -> Formula.t -> bool
end

module Make (Options : sig val profiling : bool end) = struct
  let get_time _ = unsupported ()
  let get_calls _ = unsupported ()
  let clear _ = unsupported ()
  let assume ~id f = unsupported ()
  let check () = unsupported ()
  type state = unit
  let save_state _ = unsupported ()
  let restore_state _ = unsupported ()
  let entails ~id f = unsupported ()
end
