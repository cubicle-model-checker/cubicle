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

type update = {
  up_loc : loc; (** location information *)
  up_arr : Hstring.t; (** Name of array to update (ex. [A]) *)
  up_arg : Variable.t list; (** list of universally quantified variables *)
  up_swts : (SAtom.t * Term.t) list;
  (** condition (conjunction)(ex. [C]) and term (ex. [t] *)
}
(** conditionnal updates with cases, ex. [A[j] := case | C : t | _ ...] *)

type transition_info = {
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
  tr_loc : loc; (** location information *)
}
(** type of parameterized transitions *)

type transition_func = Term.t -> op_comp -> Term.t -> Atom.t
(** functionnal form, computed during typing phase *)

(** type of parameterized transitions with function *)
type transition = {
  tr_info : transition_info;
  tr_tau : transition_func;
}

type system = {
  globals : (loc * Hstring.t * Smt.Type.t) list;
  consts : (loc * Hstring.t * Smt.Type.t) list;
  arrays : (loc * Hstring.t * (Smt.Type.t list * Smt.Type.t)) list;
  type_defs : (loc * type_constructors) list;
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


(* (\**************************************************************************\) *)
(* (\*                                                                        *\) *)
(* (\*                              Cubicle                                   *\) *)
(* (\*                                                                        *\) *)
(* (\*                       Copyright (C) 2011-2013                          *\) *)
(* (\*                                                                        *\) *)
(* (\*                  Sylvain Conchon and Alain Mebsout                     *\) *)
(* (\*                       Universite Paris-Sud 11                          *\) *)
(* (\*                                                                        *\) *)
(* (\*                                                                        *\) *)
(* (\*  This file is distributed under the terms of the Apache Software       *\) *)
(* (\*  License version 2.0                                                   *\) *)
(* (\*                                                                        *\) *)
(* (\**************************************************************************\) *)

(* exception ReachBound *)

(* type op_comp = Eq | Lt | Le | Neq *)
(* type op_arith = Plus | Minus *)

(* type sort = Glob | Arr | Constr | Var *)

(* type const = ConstInt of Num.num | ConstReal of Num.num | ConstName of Hstring.t *)

(* module MConst : sig  *)
(*   include Map.S with type key = const *)
(*   val choose : int t -> key * int *)
(*   val is_num : int t -> Num.num option *)
(* end *)

(* val compare_constants : int MConst.t -> int MConst.t -> int *)

(* type term =  *)
(*   | Const of int MConst.t *)
(*   | Elem of Hstring.t * sort *)
(*   | Access of Hstring.t * Hstring.t list *)
(*   | Arith of term * int MConst.t *)

(* val compare_term : term -> term -> int *)

(* val hash_term : term -> int *)

(* val htrue : Hstring.t *)
(* val hfalse : Hstring.t *)

(* type acc_eq = { a : Hstring.t; i: Hstring.t; e: term } *)

(* module rec Atom : sig *)
(*   type t = *)
(*     | True *)
(*     | False *)
(*     | Comp of term * op_comp * term *)
(*     | Ite of SAtom.t * t * t *)

(*   val compare : t -> t -> int *)
(*   val trivial_is_implied : t -> t -> int *)
(*   val neg : t -> t *)
(*   val hash : t -> int *)
(*   val equal : t -> t -> bool *)
(* end  *)
(* and SAtom : sig  *)
(*   include Set.S with type elt = Atom.t *)
(*   val hash : t -> int *)
(* end *)

(* val proc_vars : Hstring.t list *)
(* val proc_vars_int : int list *)
(* val alpha_vars : Hstring.t list *)
(* val fresh_vars : Hstring.t list *)

(* val add : Atom.t -> SAtom.t -> SAtom.t *)
(* val svar : (Hstring.t * Hstring.t) list -> Hstring.t -> Hstring.t *)
(* val subst_term : (Hstring.t * Hstring.t) list -> *)
(*   ?sigma_sort:(sort * sort) list -> term -> term *)
(* val subst_atom : (Hstring.t * Hstring.t) list -> *)
(*   ?sigma_sort:(sort * sort) list -> Atom.t -> Atom.t *)
(* val subst_atoms : (Hstring.t * Hstring.t) list -> *)
(*   ?sigma_sort:(sort * sort) list -> SAtom.t -> SAtom.t *)
(* val build_subst : Hstring.t list -> Hstring.t list ->  *)
(*   (Hstring.t * Hstring.t) list *)

(* module TimerSubset : Timer.S *)
(* module TimerApply  : Timer.S *)

(* module ArrayAtom : sig *)
(*   type t = Atom.t array *)
(*   val equal : t -> t -> bool *)
(*   val hash : t -> int *)
(*   val subset : t -> t -> bool *)
(*   val trivial_is_implied : t -> t -> bool *)
(*   val of_satom : SAtom.t -> t *)
(*   val to_satom : t -> SAtom.t *)
(*   val union : t -> t -> t *)
(*   val apply_subst : (Hstring.t * Hstring.t) list -> t -> t *)
(*   val nb_diff : t -> t -> int *)
(*   val compare_nb_diff : t -> t -> t -> int *)
(*   val compare_nb_common : t -> t -> t -> int *)
(*   val diff : t -> t -> t *)
(*   val alpha : t -> Hstring.t list -> Hstring.t list * t *)
(* end *)

(* type update = { *)
(*   up_arr : Hstring.t; *)
(*   up_arg : Hstring.t list; *)
(*   up_swts : (SAtom.t * term) list; *)
(* } *)

(* type transition = { *)
(*   tr_name : Hstring.t; *)
(*   tr_args : Hstring.t list; *)
(*   tr_reqs : SAtom.t; *)
(*   tr_ureq : (Hstring.t * SAtom.t list) list; *)
(*   tr_assigns : (Hstring.t * term) list; *)
(*   tr_upds : update list; *)
(*   tr_nondets : Hstring.t list; *)
(* } *)

(* type elem = Hstring.t * (Hstring.t list) *)

(* type system = { *)
(*   globals : (Hstring.t * Hstring.t) list; *)
(*   consts : (Hstring.t * Hstring.t) list; *)
(*   arrays : (Hstring.t * (Hstring.t list * Hstring.t)) list; *)
(*   type_defs : elem list; *)
(*   init : Hstring.t list * SAtom.t list; *)
(*   invs : (Hstring.t list * SAtom.t) list; *)
(*   cands : (Hstring.t list * SAtom.t) list; *)
(*   unsafe : (Hstring.t list * SAtom.t) list; *)
(*   forward : (Hstring.t list * Hstring.t list * SAtom.t) list; *)
(*   trans : transition list *)
(* } *)

(* module STerm : Set.S with type elt = term *)

(* (\* Typed AST *\) *)

(* type t_system = { *)
(*   t_globals : Hstring.t list; *)
(*   t_arrays : Hstring.t list; *)
(*   t_from : (transition * Hstring.t list * t_system) list; *)
(*   t_init : Hstring.t list * SAtom.t list; *)
(*   t_invs : (Hstring.t list * SAtom.t) list; *)
(*   t_cands : (Hstring.t list * SAtom.t) list; *)
(*   t_unsafe : Hstring.t list * SAtom.t; *)
(*   t_forward : (Hstring.t list * Hstring.t list * SAtom.t) list; *)
(*   t_arru : ArrayAtom.t; *)
(*   t_alpha : Hstring.t list * ArrayAtom.t; *)
(*   t_trans : transition list; *)
(*   mutable t_deleted : bool; *)
(*   t_nb : int; *)
(*   t_nb_father : int; *)
(*   t_glob_proc : Hstring.t list; *)
(*   t_from_forall: bool; *)
(* } *)

(* val t_system_equal : t_system -> t_system -> bool *)

(* val t_system_hash : t_system -> int *)

(* val declared_terms : ArrayAtom.t -> bool *)

(* val variables_of : SAtom.t -> STerm.t *)

(* val has_var : Hstring.t -> Atom.t -> bool *)

(* val is_int_const : const -> bool *)

(* val type_of_term : term -> Smt.Type.t *)

(* val arity : Hstring.t -> int *)

(* val all_permutations : 'a list -> 'b list -> ('a * 'b) list list *)
(* val all_instantiations : 'a list -> 'b list -> ('a * 'b) list list *)
(* val all_arrangements : int -> 'a list -> 'a list list *)
(* val permutations_missing : 'a list -> Hstring.t list -> ('a * Hstring.t) list list *)

(* val init_instances : (int, SAtom.t list list * ArrayAtom.t list list) Hashtbl.t *)

(* val fill_init_instances : Hstring.t list * SAtom.t list -> unit *)

(* val make_finite_inst_array : Hstring.t -> Hstring.t list -> Hstring.t *)

(* val has_var : Hstring.t -> Atom.t -> bool *)
  
(* val origin : t_system -> t_system *)

(* val procs_of_cube : SAtom.t -> Hstring.t list *)
