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


(** Terms, atoms and conjunctions *)


(** {2 Terms } *)

(** sort of single symbol *)
type sort =
  | Glob    (** global variable *)
  | Constr  (** constructor *)
  | Var     (** variable of the paramterized domain *)

type const = 
    | ConstInt  of Num.num 
    | ConstReal of Num.num 

module Const : sig 
  type t = const

  val is_int  : t -> bool 
  val sign    : t -> int 
  val to_num  : t -> Num.num 
  val type_of : t -> Smt.Type.t 
  val compare : t -> t -> int
  val equal   : t -> t -> bool

  val is_zero : t -> bool
  val is_one  : t -> bool
  val int_zero  : t
  val real_zero : t


  val num_equal   : t -> t -> bool
  val num_lt      : t -> t -> bool 
  val num_le      : t -> t -> bool
  val divided_by  : t -> int -> bool
  val div         : t -> Num.num-> t
  val abs         : t -> t

  val add_const : t -> t -> t 
  val add_int   : t -> Num.num -> t
  val add_real  : t -> Num.num -> t

  val neg       : t -> t

  val mult_by_int  : t -> Num.num -> t
  val mult_by_real : t -> Num.num -> t

  val cast : t -> Smt.Type.t -> t 
end

module Vea : sig
    type t =
      | Elem    of Hstring.t * sort
      | Access  of Hstring.t * Variable.t list
    val compare : t -> t -> int
end

module VMap : Map.S with type key = Vea.t

type term = 
  | Vea of Vea.t
  | Poly  of Const.t * Const.t VMap.t

val term_add : term -> term -> term
val term_mult_by_int  : term -> Num.num  -> term
val term_mult_by_real : term -> Num.num -> term
val term_mult_by_const : term -> Const.t -> term
val term_mult_by_vea  : term -> Vea.t -> term
val term_neg : term -> term
val term_mult_by_term : term -> term -> term

(** Module interface for terms *)
module Term : sig

  type t = term 

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  val subst : Variable.subst -> t -> t
  (** Apply the substitution given in argument to the term *)

  val htrue : Hstring.t
  val hfalse : Hstring.t

  val variables : t -> Variable.Set.t
  (** returns the existential variables of the given term *)

  val variables_proc : t -> Variable.Set.t
  (** same as [variables] but only return skolemized variables of the form #i *)

  val type_of : t -> Smt.Type.t
  (** returns the type of the term as it is known by the SMT solver *)

  val print : Format.formatter -> t -> unit
  (** prints a term *)

  module Set : Set.S with type elt = t
  (** set of terms *)

end


(** {2 Atoms } *)

(** comparison operators for litterals *)
type op_comp = 
  | Eq  (** equality, [=] *)
  | Lt  (** comparison less than, [<] *)
  | Le  (** comparison less or equal, [<=] *)
  | Neq (** disequality, [<>] *)


(** Interface for the atoms of the language *)
module rec Atom : sig

  (** the type of atoms *)
  type t =
    | True (** the atom [false] *)
    | False (** the atom [true] *)
    | Comp of Term.t * op_comp * Term.t
    (** application of builtin predicate (=, <>, <, <=)*)
    | Ite of SAtom.t * t * t
    (** [if-then-else] atoms that comme from computing pre-images *)

  val compare : t -> t -> int
  (** compares two atoms. The order defined by this function is important
      as it gives a way to efficiently find relevant substitutions in the module
      {! Instantiation} *)

  val trivial_is_implied : t -> t -> int
  (** return [true] if it can be immediately said that the atom in the first
      argument implies the second *)

  val neg : t -> t
  (** returns the negation of the atom *)

  val hash : t -> int
  val equal : t -> t -> bool


  val subst : Variable.subst -> t -> t
  (** Apply the substitution given in argument to the atom. This function is not
      very efficient in practice, prefer the use of {! ArrayAtom.apply_sust}
      when possible. *)

  val has_var : Variable.t -> t -> bool
  (** returns [true] if the atom contains the variable given in argument *)

  val has_vars : Variable.t list -> t -> bool
  (** returns [true] if the atom contains one of the variable given in
      argument *)

  val variables : t -> Variable.Set.t
  (** returns the existential variables of the given atom *)

  val variables_proc : t -> Variable.Set.t
  (** same as [variables] but only return skolemized variables of the form
      [#i] *)

  val print : Format.formatter -> t -> unit
  (** prints an atom *)

end


(** {2 Conjunctions } *)

(** Interface for the conjunctions of atoms seen as sets of atoms. This
    module is mutually recursive with [Atom] because of the [if-then-else] *)
and SAtom : sig
              

  include Set.S with type elt = Atom.t
  (** {e Attention}: the function [add] performs some simple semantic
      simplifications, so it is advised to not use this module for real sets of
      atoms. *)

  val equal : t -> t -> bool
  val hash : t -> int
  val subst : Variable.subst -> t -> t
  (** Apply the substitution given in argument to the conjunction *)


  val variables : t -> Variable.Set.t
  (** returns the existential variables of the given conjunction *)

  val variables_proc : t -> Variable.Set.t
  (** same as [variables] but only return skolemized variables of the form
      [#i] *)

  val print : Format.formatter -> t -> unit
  (** prints a conjunction *)

  val print_inline : Format.formatter -> t -> unit
  (** prints a conjunction on a signle line *)

end

(** Interface for the conjunctions of atoms seen as arrays of atoms. This
    is usefull for efficiently applying substitutions *)
module ArrayAtom : sig

  type t = Atom.t array
  (** values of this type should be constructed with the invariant that the
      array must be sorted at all times *)

  val equal : t -> t -> bool
  val hash : t -> int

  val subset : t -> t -> bool
  (** [subset a b] returns [true] if the elements of [a] are a subsets of the
      elements contained in [b]. [a] and [b] must be sorted with the order
      defined by {! Atom.compare} *)

  val trivial_is_implied : t -> t -> bool

  val of_satom : SAtom.t -> t
  (** transforms a conjunction if the form of a set of atoms to an equivalent
      representation with an array *)

  val to_satom : t -> SAtom.t
  (** returns the set of atoms corresponding to the conjuntion encoded
      in the array*)

  val union : t -> t -> t
  (** in fact concatenation, equivalent to taking the conjunctions of two
      conjunctinos*)

  val apply_subst : Variable.subst -> t -> t
  (** Efficient application of substitution *)

  val nb_diff : t -> t -> int
  (** returns the number of differences, i.e. atoms that are in the first
      argument but not the second. This is a measure of "difference" used for
      heuristics *)

  val compare_nb_diff : t -> t -> t -> int
  (** [compare_nb_diff a t1 t2]: based on the previous measure, this compares
      the "level" of difference with [a] *)

  val compare_nb_common : t -> t -> t -> int
  (** [compare_nb_common a t1 t2]: compares the "level of proximity" with [a].
      This is also used for heuristics *)

  val diff : t -> t -> t
  (** array form of set difference *)

  val alpha : t -> Variable.t list -> Variable.t list * t
  (** alpha renaming of process variables *)

  val print : Format.formatter -> t -> unit
  (** prints the conjunction corresponding to the array of atoms *)
end
