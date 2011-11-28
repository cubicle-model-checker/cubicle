
(* API for constructing types, terms and formula *)

type ty

val type_int : ty
val declare_type : Hstring.t -> Hstring.t list -> unit

val declare_var : Hstring.t -> ty -> unit
val declare_fun : Hstring.t -> ty list -> ty -> unit

type term
type operator = Plus | Minus | Mult | Div

val make_int : string -> term
val make_app : Hstring.t -> term list -> term
val make_arith : operator -> term -> term -> term

type formula
type comparator = Eq | Neq | Le | Lt
type combinator = And | Or | Imp | Not

val make_lit : comparator -> term list -> formula
val make_formula : combinator -> formula list -> formula


(* SMT solver interface *)

exception Sat | Unsat of Explanation.t | IDontknow

val assume : formula -> unit
val check : unit -> unit



