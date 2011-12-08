

type var = 
    { vid : int;
      pa : atom;
      na : atom;
      mutable weight : float;
      mutable seen : bool;
      mutable level : int;
      mutable reason : reason}
    
and atom = 
    { var : var;
      lit : Literal.LT.t;
      neg : atom;
      mutable watched : clause Vec.t;
      mutable is_true : bool;
      aid : int }

and clause = 
    { name : string;
      mutable atoms : atom Vec.t;
      mutable activity : float;
      mutable removed : bool;
      learnt : bool }

and reason = clause option

val dummy_var : var
val dummy_atom : atom
val dummy_clause : clause

val make_var : Literal.LT.t -> var * bool

val add_atom : Literal.LT.t -> atom 

val make_clause : string -> atom list -> int -> bool -> clause

val fresh_name : unit -> string

val fresh_lname : unit -> string

val fresh_dname : unit -> string

val to_float : int -> float

val to_int : float -> int
val made_vars_info : unit -> int * var list
val clear : unit -> unit
