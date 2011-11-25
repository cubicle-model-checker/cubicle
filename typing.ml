(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Universite Paris-Sud 11              *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Ast
open Atom

type error = 
  | UnknownConstr of string
  | UnknownVar of string
  | UnknownGlobal of string
  | DuplicateName of string
  | DuplicateTypeName of string
  | DuplicateAssign of string
  | UnknownArray of string
  | UnknownType of string
  | UnknownName of string
  | DuplicateInit of string
  | NoMoreThanOneArray
  | ClashParam of string
  | MustBeAnArray of string
  | MustBeOfType of string * AltErgo.Ty.t
  | MustBeOfTypeProc of string 
  | UncompatibleType of AltErgo.Ty.t * AltErgo.Ty.t

exception Error of error

let report fmt = function
  | UnknownConstr e ->
      fprintf fmt "unknown constructor %s" e
  | DuplicateName e ->
      fprintf fmt "duplicate name for %s" e
  | DuplicateTypeName s ->
      fprintf fmt "duplicate type name for %s" s
  | DuplicateAssign s ->
      fprintf fmt "duplicate assignment for %s" s
  | UnknownVar x ->
      fprintf fmt "unknown variable %s" x
  | UnknownArray a ->
      fprintf fmt "unknown array %s" a
  | UnknownName s ->
      fprintf fmt "unknown name %s" s
  | UnknownGlobal s ->
      fprintf fmt "unknown global %s" s
  | UnknownType s ->
      fprintf fmt "unknown type %s" s
  | DuplicateInit a ->
      fprintf fmt "duplicate initialization for %s" a
  | NoMoreThanOneArray ->
      fprintf fmt "sorry, no more than one array"
  | ClashParam x ->
      fprintf fmt "%s already used as a transition's parameter" x
  | MustBeAnArray s ->
      fprintf fmt "%s must have an array type" s
  | MustBeOfType (s, ty) ->
      fprintf fmt "%s must be of type %a" s AltErgo.Ty.print ty
  | MustBeOfTypeProc s ->
      fprintf fmt "%s must be of proc" s
  | UncompatibleType (ty1, ty2) ->
      fprintf fmt "types %a and %a are not compatible" 
	AltErgo.Ty.print ty1 AltErgo.Ty.print ty2

let error e = raise (Error e)

let rec unique error = function
  | [] -> ()
  | x :: l -> if List.mem x l then error x; unique error l

(* Type of indices *)
let ty_proc = AltErgo.Ty.Tint
let ty_int = AltErgo.Ty.Tint

(* Typing environment *)

module Env = struct

  let types : AltErgo.Ty.t Hstring.H.t = Hstring.H.create 17
  let env : (sort * AltErgo.Ty.t * AltErgo.Term.t) Hstring.H.t = Hstring.H.create 17

  let unicity x = if Hstring.H.mem env x then error (DuplicateName (Hstring.view x))

  let elems =
    let mk_elems ty x = 
      unicity x;
      let sy = AltErgo.Symbols.name ~kind:AltErgo.Symbols.Constructor  (Hstring.view x) in
      let ty_term = AltErgo.Term.make sy [] ty in
      Hstring.H.add env x (Constr, ty, ty_term)
    in
    List.iter 
      (fun (name, constrs) -> 
	 let ty = AltErgo.Ty.tsum (Hstring.view name) (List.map Hstring.view constrs) in
	 Hstring.H.add types name ty;
	 List.iter (mk_elems ty) constrs)

  let arrays = 
    List.iter
      (fun (ar, (ind, img)) ->
	 unicity ar;
	 let sy = AltErgo.Symbols.name (Hstring.view ar) in
	 let ty_ind = 
	   try Hstring.H.find types ind with Not_found -> error (UnknownType (Hstring.view ind))
	 in
	 if not (AltErgo.Ty.equal ty_ind ty_proc) then error (MustBeOfTypeProc (Hstring.view ind));
	 let ty_img = 
	   try Hstring.H.find types img with Not_found -> error (UnknownType (Hstring.view img))
	 in
	 let ty = AltErgo.Ty.Tfarray(ty_ind, ty_img) in
	 Hstring.H.add env ar (Arr, ty, AltErgo.Term.make sy [] ty) )

  let globals = 
    List.iter
      (fun (g, ty) -> 
	 unicity g;
	 try
	   let sy_g = AltErgo.Symbols.name (Hstring.view g) in
	   let ty_g = Hstring.H.find types ty in
	   Hstring.H.add env g (Glob, ty_g, AltErgo.Term.make sy_g [] ty_g)
	 with Not_found -> error (UnknownType (Hstring.view ty)) )

  let make s = elems s.elems; arrays s.arrays; globals s.globals

  let find a = Hstring.H.find env a

  let extract_infos () = Hstring.H.fold (fun g info l -> (g, info)::l) env []


  let _ = 
    Hstring.H.add types (Hstring.make "proc") ty_proc;
    Hstring.H.add types (Hstring.make "int") ty_int;
    elems [Hstring.make "bool", [Hstring.make "True"; Hstring.make "False"]]


end

let find_var args x = 
  if List.mem x args then ty_proc 
  else 
    try let _, tx, _ = Env.find x in tx with Not_found -> error (UnknownName (Hstring.view x))

let term args = function
  | Const _ -> ty_int
  | Elem e -> find_var args e
  | Arith (x, _, _) ->
      let _, ty_x, _ = 
	try Env.find x with Not_found -> error (UnknownGlobal (Hstring.view x)) in
      if ty_x <> AltErgo.Ty.Tint then error (MustBeOfType(Hstring.view x, AltErgo.Ty.Tint));
      ty_x
  | Access(a, i) -> 
      let _, ty_a, _ = 
	try Env.find a with Not_found -> error (UnknownArray (Hstring.view a)) in
      match ty_a with
	| AltErgo.Ty.Tfarray (_, ty) -> 
	    let ty_i = find_var args i in
	    if ty_i <> ty_proc then error (UncompatibleType (ty_proc, ty_i));
	    ty
	| _ -> error  (MustBeAnArray (Hstring.view a))

let atom args = function
  | True | False -> ()
  | Comp (x, op, y) -> 
      let tx = term args x in
      let ty = term args y in
      if not (AltErgo.Ty.equal tx ty) then error (UncompatibleType (tx, ty))
  | Ite _ -> assert false

let atoms args = SAtom.iter (atom args)

let init (arg, sa) =
  match arg with
    | None -> atoms [] sa
    | Some z -> atoms [z] sa

let unsafe (args, sa) = 
  unique (fun x-> error (DuplicateName (Hstring.view x))) args; 
  atoms args sa

let nondets l = 
  unique (fun c -> error (DuplicateAssign (Hstring.view c))) l;
  List.iter 
    (fun g -> 
       try
	 let _, ty, _ = Env.find g in
	 if ty <> ty_proc then error (MustBeOfTypeProc (Hstring.view g))
       with Not_found -> error (UnknownGlobal (Hstring.view g))) l

let assigns args = 
  let dv = ref [] in
  List.iter 
    (fun (g, x) ->
       if List.mem g !dv then error (DuplicateAssign (Hstring.view g));
       let _, ty_g, _ = 
	 try Env.find g with Not_found -> error (UnknownGlobal (Hstring.view g)) in
       let ty_x = term args x in
       if not (AltErgo.Ty.equal ty_g ty_x) then error (UncompatibleType (ty_x, ty_g));
       dv := g ::!dv )

let switchs args ty_e (l, ut) = 
  List.iter 
    (fun (sa, t) -> 
       atoms args sa; 
       let ty = term args t in
       if ty <> ty_e then error (UncompatibleType (ty_e, ty))) l;
  let ty = term args ut in
  if ty <> ty_e then error (UncompatibleType (ty_e, ty))

let updates args = 
  List.iter 
    (fun {up_arr=a; up_arg=arg; up_swts=swts} -> 
       if List.mem arg args then error (ClashParam (Hstring.view arg));
       let _, ty_a, _ = 
	 try Env.find a with Not_found -> error (UnknownArray (Hstring.view a)) 
       in       
       match ty_a with
	 | AltErgo.Ty.Tfarray (_, ty_e) -> switchs (arg::args) ty_e swts
	 | _ -> assert false ) 

let transitions = 
  List.iter 
    (fun ({tr_args = args} as t) -> 
       unique (fun x-> error (DuplicateName (Hstring.view x))) args; 
       atoms args t.tr_reqs;
       (match t.tr_ureq with None -> () | Some (x, sa) -> atoms (x::args) sa);
       updates args t.tr_upds;
       assigns args t.tr_assigns;
       nondets t.tr_nondets)

let system s = 
  Env.make s;
  init s.init;
  unsafe s.unsafe;
  transitions s.trans;
  let args, p = s.unsafe in
  let arru = ArrayAtom.of_satom p in
  { 
    t_from = [];
    t_env = Env.env;
    t_init = s.init;
    t_invs = s.invs;
    t_unsafe = s.unsafe;
    t_arru = arru;
    t_alpha = ArrayAtom.alpha arru args;
    t_trans = s.trans;
    t_deleted = false;
  }
