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
open Types

exception ReachBound

type dnf = SAtom.t list

type type_constructors = Hstring.t * (Hstring.t list)

type update = {
  up_arr : Hstring.t;
  up_arg : Variable.t list;
  up_swts : (SAtom.t * Term.t) list;
}

type transition = {
  tr_name : Hstring.t;
  tr_args : Variable.t list;
  tr_reqs : SAtom.t;
  tr_ureq : (Variable.t * dnf) list;
  tr_assigns : (Hstring.t * Term.t) list;
  tr_upds : update list;
  tr_nondets : Hstring.t list;
}

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

(* Typed AST *)

type kind = Approx | Node | Inv

type node_cube =
    { 
      cube : Cube.t;
      alpha : Variable.t list * ArrayAtom.t;
      tag : int;
      kind : kind;
      depth : int;
      mutable deleted : bool;
      from : trace;
    }
and trace = (transition * Variable.t list * node_cube) list

type t_system = {
  t_globals : Hstring.t list;
  t_arrays : Hstring.t list;
  t_init : Variable.t list * dnf;
  t_init_instances : (int, (dnf list * ArrayAtom.t list list)) Hashtbl.t;
  t_invs : node_cube list;
  t_unsafe : node_cube list;
  t_trans : transition list;
}


let all_var_terms procs {t_globals = globals; t_arrays = arrays} =
  let acc, gp = 
    List.fold_left 
      (fun (acc, gp) g -> 
	Term.Set.add (Elem (g, Glob)) acc, gp
      ) (Term.Set.empty, []) globals
  in
  List.fold_left (fun acc a ->
    let indexes = Variable.all_arrangements_arity a (procs@gp) in
    List.fold_left (fun acc lp ->
      Term.Set.add (Access (a, lp)) acc)
      acc indexes)
    acc arrays
