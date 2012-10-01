(**************************************************************************)
(*                                                                        *)
(*                          Alt-Ergo light                                *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                      Universite Paris-Sud 11                           *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

(** {b The Alt-Ergo light SMT library}

    This SMT solver is derived from {{:http://alt-ergo.lri.fr} Alt-Ergo}. It
    uses an efficient SAT solver and supports the following quantifier free
    theories:
    - Equality and uninterpreted functions
    - Arithmetic (linear, non-linear, integer, reals)
    - Enumerated data-types

 *)

type error = 
  | DuplicateTypeName of Hstring.t
  | DuplicateSymb of Hstring.t
  | UnknownType of Hstring.t
  | UnknownSymb of Hstring.t

exception Error of error

(** Typing of terms *)
module Type : sig

  (** {2 Builtin types } *)

  type t = Hstring.t

  val type_int : t
  (** The type of integers *)

  val type_real : t
  (** The type of reals *)

  val type_bool : t
  (** The type of booleans *)

  val type_proc : t
  (** The type processes (identifiers) *)

  val declare : Hstring.t -> Hstring.t list -> unit
  (** {ul {- [declare_type (n, cstrs)] declares a new enumerated data-type with
      name [n] and constructors [cstrs].}
      {- [declare_type (n, [])] declares a new abstract type with name [n].}}*)

  val all_constructors : unit -> Hstring.t list
  (** [all_constructors ()] returns a list of all the defined constructors. *)

end


(** {2 Symbols }
    
*)

module Symbol : sig
    
  type t = Hstring.t
    
  val declare : Hstring.t -> t list -> t -> unit
  (** [declare_name s [arg1;...;argn] out] declares a new function
      symbol with type [ (arg1, ... , argn) -> out] *)
    
  (** {2 Querying about types } *)
    
  val find : t -> Type.t list * Type.t
    (** [find x] returns the type of x. *)
    
  val has_abstract_type : t -> bool
    (** [has_abstract_type x] is [true] if the type of x is abstract. *)
    
  val has_type_proc : t -> bool
  (** [has_type_proc x] is [true] if x has the type of a process
      identifier. *)
        
  val declared : t -> bool
  (** [declared x] is [true] if [x] is already declared. *)
      
end

(** {2 Variants }
      
    The types of symbols (when they are enumerated data types) can be refined
    to substypes of their original type (i.e. a subset of their constructors).
*)
  
module Variant : sig

  val init : (Symbol.t * Type.t) list -> unit
  (** [init l] where [l] is a list of pairs [(s,ty)] initializes the
      constructors of each [s] to its original type [ty].
      
      This function must be called with a list of all symbols before
      attempting to refine the types. *)

  val close : unit -> unit
  (** [close ()] will compute the smallest type possible for each symbol.

      This function must be called when all information has been added.*)

  val assign_constr : Symbol.t -> Hstring.t -> unit
    (** [assign_constr s cstr] will add the constructor cstr to the refined
        type of s *)

  val assign_var : Hstring.t -> Hstring.t -> unit
    (** [assign_var x y] will add the constraint that the type of [y] is a
        subtype of [x] (use this function when [x := y] appear in your 
        program *)

  val print : unit -> unit
    (** [print ()] will output the computed refined types on std_err. This
        function is here only for debugging purposes. Use it afer [close ()].*)

  val get_variants : Symbol.t -> Hstring.HSet.t
  (** [get_variants s] returns a set of constructors, which is the refined
      type of [s].*)

end

(** Building terms *)
module Term : sig
  type t
  (** The type of terms *)

  (** The type of operators *)
  type operator = 
    | Plus (** [+] *)
    | Minus (** [-] *)
    | Mult (** [*] *) 
    | Div (** [/] *)
    | Modulo (** [mod] *)

  val make_int : Num.num -> t
  (** [make_int n] creates an integer constant of value [n]. *)

  val make_real : Num.num -> t
  (** [make_real n] creates an real constant of value [n]. *)

  val make_app : Hstring.t -> t list -> t
  (** [make_app f l] creates the application of function symbol [f] to a list
      of terms [l]. *)

  val make_arith : operator -> t -> t -> t
  (** [make_arith op t1 t2] creates the term [t1 <op> t2]. *)

  val is_int : t -> bool
  (** [is_int x] is [true] if the term [x] has type int *)

  val is_real : t -> bool
  (** [is_real x] is [true] if the term [x] has type real *)

  val t_true : t
  (** [t_true] is the boolean term [true] *)

  val t_false : t
  (** [t_false] is the boolean term [false] *)

end


(** Building formulas *)
module Formula : sig

  (** The type of comparators: *)
  type comparator = 
    | Eq  (** equality ([=]) *)
    | Neq (** disequality ([<>]) *)
    | Le  (** inequality ([<=]) *)
    | Lt  (** strict inequality ([<]) *)

  (** The type of operators *)
  type combinator = 
    | And (** conjunction *)
    | Or  (** disjunction *)
    | Imp (** implication *)
    | Not (** negation *)

  (** The type of ground formulas *)
  type ground = 
    | Lit of Literal.LT.t  
    | Comb of combinator * ground list

  (** The type of lemmas or universally quantified formulas.
      {b Not implemented }*)
  type lemma = Hstring.t list * ground

  (** The type of formulas. {b Not implemented } *)
  type t = Ground of ground | Lemma of lemma


  val f_true : ground
  (** The formula which represents [true]*)

  val f_false : ground
  (** The formula which represents [false]*)

  val make_lit : comparator -> Term.t list -> ground
  (** [make_lit cmp [t1; t2]] creates the litteral [(t1 <cmp> t2)]. *)

  val make : combinator -> ground list -> ground
  (** [make_lit cmb [f_1; ...; f_n]] creates the formula
      [(f_1 <cmb> ... <cmb> f_n)]. *)

  val make_cnf : ground -> Literal.LT.t list list
  (** [make_cnf f] returns a conjunctive normal form of [f] under the form: a
      list (which is a conjunction) of lists (which are disjunctions) of
      litterals. *)

  val print : Format.formatter -> t -> unit
  (** [print fmt f] prints the formula on the formatter [fmt].*)

end

(* SMT solver interface *)

exception Unsat of int list
(** The exception raised by {! Smt.Solver.check} when the formula is
    unsatisfiable. *)


(** The SMT solver *)
module type Solver = sig

  (** This SMT solver is imperative in the sense that it maintains a global
      context. To create different instances of Alt-Ergo light use the
      functor {! Smt.Make}. *)

  (** {2 Profiling functions} *)

  val get_time : unit -> float
  (** [get_time ()] returns the cumulated time spent in the solver in seconds.
  *)
  val get_calls : unit -> int
  (** [get_calls ()] returns the cumulated number of calls to {! check}.*)

  (** {2 Main API of the solver} *)

  val clear : unit -> unit
  (** [clear ()] clears the context of the solver. Use this after {! check}
      raised {! Unsat} or if you want to restart the solver. *)


  val assume : profiling:bool -> Formula.t -> cnumber:int -> unit
  (** [assume ~profiling:b f id] adds the formula [f] to the context of the
      solver with idetifier [id].
      This function only performs unit propagation.
      
      @param profiling if set to [true] then profiling information (time) will
      be computed (expensive because of system calls).
      
      {b Raises} {! Unsat} if the context becomes inconsistent after unit
      propagation. *)

  val check : profiling:bool -> unit  
  (** [check ~profiling:b] runs Alt-Ergo light on its context. If [()] is
      returned then the context is satifiable.
      
      @param profiling if set to [true] then profiling information (time) will
      be computed (expensive because of system calls).
      
      {b Raises} {! Unsat} [[id_1; ...; id_n]] if the context is unsatisfiable.
      [id_1, ..., id_n] is the unsat core (returned as the identifiers of the
      formulas given to the solver). *)

end

(** Functor to create several instances of the solver *)
module Make (Dummy : sig end) : Solver

