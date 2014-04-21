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

open Types

(** {b Abstract syntax tree and transition systems } *)


type dnf = SAtom.t list
(** Disjunctive normal form: each element of the list is a disjunct *)

type type_constructors = Hstring.t * (Hstring.t list)
(** Type and constructors declaration: [("t", ["A";"B"])] represent the
    declaration of type [t] with two constructors [A] and [B] *)

type update = {
  up_arr : Hstring.t; (** Name of array to update (ex. [A]) *)
  up_arg : Variable.t list; (** list of universally quantified variables *)
  up_swts : (SAtom.t * Term.t) list;
  (** condition (conjunction)(ex. [C]) and term (ex. [t] *)
}
(** conditionnal updates with cases, ex. [A[j] := case | C:t | _ ...] *)

type transition = {
  tr_name : Hstring.t; (** name of the transition *)
  tr_args : Variable.t list;
  (** existentially quantified parameters of the transision *)
  tr_reqs : SAtom.t; (** guard *)
  tr_ureq : (Variable.t * dnf) list;
  (** global condition of the guard, i.e. universally quantified DNF *)
  tr_assigns : (Hstring.t * Term.t) list; (** updates of global variables *)
  tr_upds : update list; (** updates of arrays *)
  tr_nondets : Hstring.t list;
  (** non deterministic updates (only for global variables) *)
  tr_tau : Term.t -> op_comp -> Term.t -> Atom.t;
  (** functionnal form, computed during typing phase *)
}
(** type of parameteried transitions *)

type system = {
  globals : (Hstring.t * Smt.Type.t) list;
  consts : (Hstring.t * Smt.Type.t) list;
  arrays : (Hstring.t * (Smt.Type.t list * Smt.Type.t)) list;
  type_defs : type_constructors list;
  init : Variable.t list * dnf;
  invs : (Variable.t list * SAtom.t) list;
  unsafe : (Variable.t list * SAtom.t) list;  
  trans : transition list
}
(** type of untyped transition systems *)

(* Typed AST *)

type kind = Approx | Orig | Node | Inv
(** kind of nodes (approximation, original unsafe formula, reguar node or user
    supplied invariant )*)

type node_cube =
    { 
      cube : Cube.t;
      tag : int;
      kind : kind;
      depth : int;
      mutable deleted : bool;
      from : trace;
    }
(** the type of nodes, i.e. cubes with extra information *)
and trace = (transition * Variable.t list * node_cube) list
(** type of error traces, also the type of history of nodes *)

type t_system = {
  t_globals : Hstring.t list; (** Global variables *)
  t_arrays : Hstring.t list; (** Array names *)
  t_init : Variable.t list * dnf;
  (** Formula describing the initial states of the system, universally
      quantified DNF : \forall i. c1 \/ c2 \/ ... *)
  t_init_instances : (int, (dnf list * ArrayAtom.t list list)) Hashtbl.t;
  (** pre-computed instances of the initial formula *)
  t_invs : node_cube list;
  (** user supplied invariants in negated form *)
  t_unsafe : node_cube list;
  (** unsafe formulas (in the form of cubes *)
  t_trans : transition list;
  (** transition relation in the form of a list of transitions *)
}
(** type of typed transition systems *)
