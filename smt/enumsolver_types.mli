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



type ident =
    {
      iname : Hstring.t;
      mask : int;
      mutable ivalues : (atom * int) Vec.t;
      ivars : var Vec.t;
    }

and var =
    {  vid : int;
       ident : ident;
       pa : atom;
       na : atom;
       mutable weight : float;
       mutable seen : bool;
       mutable level : int;
       mutable reason: reason;
       mutable vpremise : premise}
      
and atom = 
    { aid : int;
      var : var;
      value : int;
      neg : atom;
      mutable is_true : bool;
      mutable watched : clause Vec.t;}


and clause = 
    { name : string; 
      mutable atoms : atom Vec.t ; 
      mutable activity : float;
      mutable removed : bool;
      learnt : bool;
      cpremise : premise }


and reason = clause option

and premise = clause list

val cpt_mk_var : int ref

val dummy_var : var
val dummy_atom : atom
val dummy_clause : clause

(* val make_var : Hstring.t -> int -> int -> atom *)

val add_atom :
  (atom * clause * int) list ref -> 
  (Hstring.t * int * int) -> atom

val make_clause : string -> atom list -> int -> bool -> premise-> clause

val fresh_name : unit -> string

val fresh_lname : unit -> string

val fresh_dname : unit -> string

val to_float : int -> float

val to_int : float -> int
val made_vars_info : unit -> int * atom list
val clear : unit -> unit

(* val is_top : atom -> bool *)
(* val is_bottom : atom -> bool *)
val same_ident : atom -> atom -> bool
val is_bottom : atom -> bool

val enqueue_ident : atom -> (atom * clause * int) list
val pop_ident : atom -> unit
val check_bottom_clause : atom -> (clause) option

module Debug: sig
    
  val atom : Format.formatter -> atom -> unit
  val atoms_list : Format.formatter -> atom list -> unit
    
  val clause : Format.formatter -> clause -> unit

end


val is_attached : clause -> bool
