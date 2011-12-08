(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Ast
open Atom

type error = 
  | UnknownConstr of Hstring.t
  | UnknownVar of Hstring.t
  | UnknownGlobal of Hstring.t
  | DuplicateName of Hstring.t
  | DuplicateTypeName of Hstring.t
  | DuplicateAssign of Hstring.t
  | UnknownArray of Hstring.t
  | UnknownType of Hstring.t
  | UnknownName of Hstring.t
  | DuplicateInit of Hstring.t
  | NoMoreThanOneArray
  | ClashParam of Hstring.t
  | MustBeAnArray of Hstring.t
  | MustBeOfType of Hstring.t * Hstring.t
  | MustBeOfTypeProc of Hstring.t 
  | UncompatibleType of Hstring.t * Hstring.t
  | NotATerm of Hstring.t

exception Error of error

let report fmt = function
  | UnknownConstr e ->
      fprintf fmt "unknown constructor %a" Hstring.print e
  | DuplicateName e ->
      fprintf fmt "duplicate name for %a" Hstring.print e
  | DuplicateTypeName s ->
      fprintf fmt "duplicate type name for %a" Hstring.print s
  | DuplicateAssign s ->
      fprintf fmt "duplicate assignment for %a" Hstring.print s
  | UnknownVar x ->
      fprintf fmt "unknown variable %a" Hstring.print x
  | UnknownArray a ->
      fprintf fmt "unknown array %a" Hstring.print a
  | UnknownName s ->
      fprintf fmt "unknown name %a" Hstring.print s
  | UnknownGlobal s ->
      fprintf fmt "unknown global %a" Hstring.print s
  | UnknownType s ->
      fprintf fmt "unknown type %a" Hstring.print s
  | DuplicateInit a ->
      fprintf fmt "duplicate initialization for %a" Hstring.print a
  | NoMoreThanOneArray ->
      fprintf fmt "sorry, no more than one array"
  | ClashParam x ->
      fprintf fmt "%a already used as a transition's parameter" Hstring.print x
  | MustBeAnArray s ->
      fprintf fmt "%a must have an array type" Hstring.print s
  | MustBeOfType (s, ty) ->
      fprintf fmt "%a must be of type %a" Hstring.print s Hstring.print ty
  | MustBeOfTypeProc s ->
      fprintf fmt "%a must be of proc" Hstring.print s
  | UncompatibleType (ty1, ty2) ->
      fprintf fmt "types %a and %a are not compatible" 
	Hstring.print ty1 Hstring.print ty2
  | NotATerm s -> fprintf fmt "%a is not a term" Hstring.print s

let error e = raise (Error e)

let rec unique error = function
  | [] -> ()
  | x :: l -> if Hstring.list_mem x l then error x; unique error l

let term args = function
  | Const _ -> Smt.Typing.type_int
  | Elem (e, Var) ->
      if not (Hstring.list_mem e args) then error (UnknownName e);
      Smt.Typing.type_proc
  | Elem (e, _) -> 
      let l, t = Smt.Typing.find e in
      if l <> [] then error (NotATerm e);
      t
  | Arith (x, (Var | Constr | Arr), _, _) ->
      error (MustBeOfType (x, Smt.Typing.type_int))
  | Arith (x, _, _, _) ->
      begin
	try 
	  let args, ret = Smt.Typing.find x in
	  if args <> [] then error (NotATerm x);
	  if not (Hstring.equal ret Smt.Typing.type_int) then 
	    error (MustBeOfType(x, Smt.Typing.type_int));
	  ret
	with Not_found -> error (UnknownGlobal x)
      end
  | Access(a, i) -> 
      let args_a, ty_a = 
	try Smt.Typing.find a with Not_found -> error (UnknownArray a) in
      let args_i, ty_i = 
	try Smt.Typing.find i with Not_found -> error (UnknownName i)
      in
      if args_a = [] then error (MustBeAnArray a);
      if args_i <> [] then error (NotATerm i);
      if not (Hstring.equal ty_i Smt.Typing.type_proc) then
	error (MustBeOfTypeProc i);	    
      ty_a

let atom args = function
  | True | False -> ()
  | Comp (x, op, y) -> 
      let tx = term args x in
      let ty = term args y in
      if not (Hstring.equal tx ty) then error (UncompatibleType (tx, ty))
  | Ite _ -> assert false

let atoms args = SAtom.iter (atom args)

let init (arg, sa) =
  match arg with
    | None -> atoms [] sa
    | Some z -> atoms [z] sa

let unsafe (args, sa) = 
  unique (fun x-> error (DuplicateName x)) args; 
  atoms args sa

let nondets l = 
  unique (fun c -> error (DuplicateAssign c)) l;
  List.iter 
    (fun g -> 
       try
	 let args_g, ty_g = Smt.Typing.find g in
	 if args_g <> [] then error (NotATerm g);
	 if not (Hstring.equal ty_g Smt.Typing.type_proc) then 
	   error (MustBeOfTypeProc g)
       with Not_found -> error (UnknownGlobal g)) l

let assigns args = 
  let dv = ref [] in
  List.iter 
    (fun (g, x) ->
       if Hstring.list_mem g !dv then error (DuplicateAssign g);
       let args_g, ty_g = 
	 try Smt.Typing.find g with Not_found -> error (UnknownGlobal g) in
       if args_g <> [] then error (NotATerm g);
       let ty_x = term args x in
       if not (Hstring.equal ty_g ty_x) then 
	 error (UncompatibleType (ty_x, ty_g));
       dv := g ::!dv)

let switchs args ty_e (l, ut) = 
  List.iter 
    (fun (sa, t) -> 
       atoms args sa; 
       let ty = term args t in
       if not (Hstring.equal ty ty_e) then 
	 error (UncompatibleType (ty_e, ty))) l;
  let ty = term args ut in
  if not (Hstring.equal ty ty_e) then error (UncompatibleType (ty_e, ty))

let updates args = 
  List.iter 
    (fun {up_arr=a; up_arg=j; up_swts=swts} -> 
       if Hstring.list_mem j args then error (ClashParam j);
       let args_a, ty_a = 
	 try Smt.Typing.find a with Not_found -> error (UnknownArray a)
       in       
       if args_a = [] then error (MustBeAnArray a);
       switchs (j::args) ty_a swts) 

let transitions = 
  List.iter 
    (fun ({tr_args = args} as t) -> 
       unique (fun x-> error (DuplicateName x)) args; 
       atoms args t.tr_reqs;
       (match t.tr_ureq with None -> () | Some (x, sa) -> atoms (x::args) sa);
       updates args t.tr_upds;
       assigns args t.tr_assigns;
       nondets t.tr_nondets)

let init_global_env s = 
  List.iter Smt.Typing.declare_type s.type_defs;
  List.iter 
    (fun (n, t) -> Smt.Typing.declare_name n [] t) s.globals;
  List.iter 
    (fun (n, (arg, ret)) -> Smt.Typing.declare_name n [arg] ret) s.arrays

let init_proc () = 
  List.iter 
    (fun n -> Smt.Typing.declare_name n [] Smt.Typing.type_proc) proc_vars

let system s = 
  init_global_env s;
  init s.init;
  unsafe s.unsafe;
  transitions s.trans;
  let args, p = s.unsafe in
  let arru = ArrayAtom.of_satom p in
  { 
    t_from = [];
    t_init = s.init;
    t_invs = s.invs;
    t_unsafe = s.unsafe;
    t_arru = arru;
    t_alpha = ArrayAtom.alpha arru args;
    t_trans = s.trans;
    t_deleted = false;
    t_nb = 0;
    t_nb_father = -1;
  }
