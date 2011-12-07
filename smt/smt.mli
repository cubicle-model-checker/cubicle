

exception AlreadyDeclared of Hstring.t
exception Undefined of Hstring.t

(* API for the construction of types, terms and formulas *)

type ty

val type_int : ty
val type_bool : ty

val declare_type : Hstring.t -> Hstring.t list -> unit
val declare_name : Hstring.t -> ty list -> ty -> unit

type term
type operator = Plus | Minus | Mult | Div | Modulo

val vrai : term
val faux : term
val make_int : string -> term
val make_app : Hstring.t -> term list -> term
val make_arith : operator -> term -> term -> term

type formula
type comparator = Eq | Neq | Le | Lt
type combinator = And | Or | Imp | Not

val make_lit : comparator -> term list -> formula
val make_formula : combinator -> formula list -> formula

(* SMT solver interface *)

exception Sat 
exception Unsat of Explanation.t 
exception IDontknow

val clear : unit -> unit
val assume : formula -> unit
val check : unit -> unit



