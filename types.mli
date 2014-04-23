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
  | Glob (** global variable *)
  | Constr (** constructor *)
  | Var (** variable of the paramterized domain *)

(** constant: it can be an integer, a real or a constant name *)
type const =
    ConstInt of Num.num | ConstReal of Num.num | ConstName of Hstring.t
                                                                
module MConst : sig 
  include Map.S with type key = const
  val choose : int t -> key * int
  val is_num : int t -> Num.num option
end

val compare_constants : int MConst.t -> int MConst.t -> int
val add_constants : int MConst.t -> int MConst.t -> int MConst.t
val const_sign : int MConst.t -> int option
val const_nul : int MConst.t -> bool
val mult_const : int -> int MConst.t -> int MConst.t


(** the type of terms *)
type term =
  | Const of int MConst.t
  (** constant given as a map. [1*2 + 3*c] is the map [[2 -> 1; c -> 3]] *)
  | Elem of Hstring.t * sort
  (** element, can be a variable or a process *)
  | Access of Hstring.t * Variable.t list
  (** an access to an array *)
  | Arith of term * int MConst.t
  (** arithmetic term: [Arith (t, c)] is the term [t + c] *)


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
  (** same as [variables] but only return skolemized variables of the form #i *)

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
  (** same as [variables] but only return skolemized variables of the form #i *)

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
