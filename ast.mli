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
open Util


(** Abstract syntax tree and transition systems *)


(** {2 Untyped transition system} *)


type dnf = SAtom.t list
(** Disjunctive normal form: each element of the list is a disjunct *)

type type_constructors = Hstring.t * (Hstring.t list)
(** Type and constructors declaration: [("t", ["A";"B"])] represents the
    declaration of type [t] with two constructors [A] and [B]. If the
    list of constructors is empty, the type [t] is defined abstract. *)

type swts = (SAtom.t * Term.t) list
(** The type of case switches case | c1 : t1 | c2 : t2 | _ : tn *)

type glob_update = UTerm of Term.t | UCase of swts
(** Updates of global variables, can be a term or a case construct. *)

type update = {
  up_loc : loc; (** location information *)
  up_arr : Hstring.t; (** Name of array to update (ex. [A]) *)
  up_arg : Variable.t list; (** list of universally quantified variables *)
  up_swts : swts;
  (** condition (conjunction)(ex. [C]) and term (ex. [t] *)
}
(** conditionnal updates with cases, ex. [A[j] := case | C : t | _ ...] *)


type lock =
  | VarLock of Term.t * Hstring.t

type lock_uses =
  | Condition of lock
  | Lock of lock 
  | Unlock of lock 
  | Wait of lock 
  | Notify of lock 
  | NotifyAll of lock 


type transition_info = {
  tr_name : Hstring.t; (** name of the transition *)
  tr_args : (Variable.t * Hstring.t option) list;
  tr_process : Variable.t option;
  (** existentially quantified parameters of the transision *)
  tr_reqs : SAtom.t * loc; (** guard *)
  tr_ureq : (Variable.t * dnf * loc) list;
  (** global condition of the guard, i.e. universally quantified DNF *)
  tr_lets : (Hstring.t * Term.t) list;
  tr_assigns : (Hstring.t * glob_update * loc) list; (** updates of global variables *)
  tr_locks : lock_uses list * loc; 
  tr_upds : update list; (** updates of arrays *)
  tr_nondets : Hstring.t list;
  (** non deterministic updates (only for global variables) *)
  tr_loc : loc; (** location information *)
}
(** type of parameterized transitions *)

type transition_func = Term.t -> op_comp -> Term.t -> Atom.t
(** functionnal form, computed during typing phase *)

(** type of parameterized transitions with function *)
type transition = {
  tr_info : transition_info;
  tr_tau : transition_func;
  tr_reset : unit -> unit;
}

type type_defs =
  | Constructors of (loc * type_constructors)
  | ProcSubsets of (loc * Hstring.t)


type system = {
  globals : (loc * Hstring.t * Smt.Type.t) list;
  consts : (loc * Hstring.t * Smt.Type.t) list;
  arrays : (loc * Hstring.t * (Hstring.t list * Hstring.t)) list;
  type_defs : type_defs list;
  init : loc * Variable.t list * dnf;
  invs : (loc * Variable.t list * SAtom.t) list;
  unsafe : (loc * Variable.t list * SAtom.t) list;  
  trans : transition_info list;
}
(** type of untyped transition systems constructed by parsing *)


(** {2 Typed transition system} *)

(** the kind of nodes *)
type kind = 
  | Approx (** approximation *)
  | Orig   (** original unsafe formula *)
  | Node   (** reguar node *)
  | Inv    (** or user supplied invariant*)


type node_cube =
    { 
      cube : Cube.t;          (** the associated cube *)
      tag : int;              (** a unique tag (negative for approximations
                                  and positive otherwise) *)
      kind : kind;            (** the kind of the node *)
      depth : int;            (** its depth in the search tree*)
      mutable deleted : bool; (** flag changed when the {e a-posteriori}
                                  simplification detects subsumption
                                  (see {! Cubetrie.delete_subsumed}) *)
      from : trace;           (** history of the node *)
    }
(** the type of nodes, i.e. cubes with extra information *)

and trace_step = transition_info * Variable.t list * node_cube
(** type of elementary steps of error traces *)

and trace = trace_step list
(** type of error traces, also the type of history of nodes *)

type init_instance = {
  init_cdnf : dnf list; (** DNFs for initial states *)
  init_cdnf_a : ArrayAtom.t list list;
  (** DNFs for initial states in array form *)
  init_invs : ArrayAtom.t list;
  (** Instantiated negated user supplied invariants *)
}
(** Type of instantiated initial formulas *)

type t_system = {
  t_globals : Hstring.t list; (** Global variables *)
  t_consts : Hstring.t list; (** Existential constants *)
  t_arrays : Hstring.t list; (** Array names *)
  t_init : Variable.t list * dnf;
  (** Formula describing the initial states of the system, universally
      quantified DNF : \forall i. c1 \/ c2 \/ ... *)
  t_init_instances : (int, init_instance) Hashtbl.t;
  (** pre-computed instances of the initial formula with invariants *)
  t_invs : node_cube list;
  (** user supplied invariants in negated form *)
  t_unsafe : node_cube list;
  (** unsafe formulas (in the form of cubes *)
  t_trans : transition list;
  (** transition relation in the form of a list of transitions *)
}
(** type of typed transition systems *)
