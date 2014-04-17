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

exception ReachBound

type dnf = Atom.Set.t list

type type_constructors = Hstring.t * (Hstring.t list)

type update = {
  up_arr : Hstring.t;
  up_arg : Variable.t list;
  up_swts : (Atom.Set.t * Term.t) list;
}

type transition = {
  tr_name : Hstring.t;
  tr_args : Variable.t list;
  tr_reqs : Atom.Set.t;
  tr_ureq : (Variable.t * dnf) list;
  tr_assigns : (Hstring.t * Term.t) list;
  tr_upds : update list;
  tr_nondets : Hstring.t list;
}

type system = {
  globals : (Hstring.t * Smt.Type.t) list;
  consts : (Hstring.t * Smt.Type.t) list;
  arrays : (Hstring.t * (Smt.Type.t list * Smt.Type.t)) list;
  type_defs : type_constructors list;
  init : Variable.t list * dnf;
  invs : (Variable.t list * Atom.Set.t) list;
  unsafe : (Variable.t list * Atom.Set.t) list;  
  trans : transition list
}

(* Typed AST *)

type t_system = {
  t_globals : Hstring.t list;
  t_arrays : Hstring.t list;
  t_init : Variable.t list * dnf;
  t_init_instances : (int, (dnf list, Atom.Array.t list list)) Hashtbl.t;
  t_invs : Cube.t list;
  t_unsafe : Cube.t list;
  t_trans : transition list;
}

val all_var_terms : Variable.t list -> t_system -> Term.Set.t
