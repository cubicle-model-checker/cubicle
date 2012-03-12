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
  | MustBeNum of Hstring.t
  | MustBeOfTypeProc of Hstring.t 
  | IncompatibleType of Hstring.t list * Hstring.t * Hstring.t list * Hstring.t
  | NotATerm of Hstring.t

exception Error of error

let print_htype fmt (args, ty) =
  fprintf fmt "%a%a" 
    (fun fmt -> List.iter (fprintf fmt "%a -> " Hstring.print)) args
    Hstring.print ty
       
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
  | MustBeNum s ->
      fprintf fmt "%a must be of type int or real" Hstring.print s
  | MustBeOfTypeProc s ->
      fprintf fmt "%a must be of proc" Hstring.print s
  | IncompatibleType (args1, ty1, args2, ty2) ->
      fprintf fmt "types %a and %a are not compatible" 
	print_htype (args1, ty1) print_htype (args2, ty2)
  | NotATerm s -> fprintf fmt "%a is not a term" Hstring.print s

let error e = raise (Error e)

let rec unique error = function
  | [] -> ()
  | x :: l -> if Hstring.list_mem x l then error x; unique error l

let unify (args_1, ty_1) (args_2, ty_2) =
  if not (Hstring.equal ty_1 ty_2) || Hstring.compare_list args_1 args_2 <> 0
  then error (IncompatibleType (args_1, ty_1, args_2, ty_2))

let refinements = Hstring.H.create 17

let infer_type x1 x2 =
  try
    let h1 = match x1 with
      | Const _ | Arith _ -> raise Exit
      | Elem (h1, _) | Access (h1, _) -> h1
    in
    let ref_ty, ref_cs =
      try Hstring.H.find refinements h1 with Not_found -> [], [] in
    match x2 with
      | Elem (e2, Constr) -> Hstring.H.add refinements h1 (e2::ref_ty, ref_cs)
      | Elem (e2, Glob) -> Hstring.H.add refinements h1 (ref_ty, e2::ref_cs)
      | _ -> ()
  with Exit -> ()

let refinement_cycles () = (* TODO *) ()

let term args = function
  | Const cs ->
      let c, _ = MConst.choose cs in
      (match c with
	| ConstInt _ -> [], Smt.Typing.type_int
	| ConstReal _ -> [], Smt.Typing.type_real
	| ConstName x -> 
	    try Smt.Typing.find x with Not_found -> error (UnknownName x))
  | Elem (e, Var) ->
      if Hstring.list_mem e args then [], Smt.Typing.type_proc
      else begin 
	try Smt.Typing.find e with Not_found -> error (UnknownName e)
      end
  | Elem (e, _) -> Smt.Typing.find e
  | Arith (x, (Var | Constr | Arr), _) ->
      error (MustBeNum x)
  | Arith (x, _, _) ->
      begin
	try 
	  let args, ret = Smt.Typing.find x in
	  if args <> [] then error (NotATerm x);
	  if not (Hstring.equal ret Smt.Typing.type_int) 
	    && not (Hstring.equal ret Smt.Typing.type_real) then 
	    error (MustBeNum x);
	  args, ret
	with Not_found -> error (UnknownGlobal x)
      end
  | Access(a, i) -> 
      let args_a, ty_a = 
	try Smt.Typing.find a with Not_found -> error (UnknownArray a) in
      let ty_i =
	if Hstring.list_mem i args then Smt.Typing.type_proc
	else 
	  try 
	    let ia, tyi = Smt.Typing.find i in
	    if ia <> [] then error (MustBeOfTypeProc i);
	    tyi
	  with Not_found -> error (UnknownName i) 
      in
      if args_a = [] then error (MustBeAnArray a);
      if not (Hstring.equal ty_i Smt.Typing.type_proc) then
	error (MustBeOfTypeProc i);	    
      [], ty_a

let assignment ?(init_variant=false) g x (_, ty) = 
  if ty = Smt.Typing.type_proc 
    || ty = Smt.Typing.type_bool
    || ty = Smt.Typing.type_int
  then ()
  else
    match x with
      | Elem (n, Constr) -> 
	  Smt.Typing.Variant.assign_constr g n
      | Elem (n, _) | Access (n, _) -> 
	  Smt.Typing.Variant.assign_var g n;
	  if init_variant then 
	    Smt.Typing.Variant.assign_var n g
      | _ -> ()

let atom init_variant args = function
  | True | False -> ()
  | Comp (Elem(g, Glob) as x, Eq, y)
  | Comp (y, Eq, (Elem(g, Glob) as x))
  | Comp (y, Eq, (Access(g, _) as x))
  | Comp (Access(g, _) as x, Eq, y) -> 
      let ty = term args y in
      unify (term args x) ty;
      if init_variant then assignment ~init_variant g y ty
  | Comp (x, op, y) -> 
      unify (term args x) (term args y)
  | Ite _ -> assert false

let atoms ?(init_variant=false) args = SAtom.iter (atom init_variant args)

let init (arg, sa) =
  match arg with
    | None -> atoms ~init_variant:true [] sa
    | Some z -> atoms ~init_variant:true  [z] sa

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
       let ty_g = 
	 try Smt.Typing.find g with Not_found -> error (UnknownGlobal g) in
       let ty_x = term args x in
       unify ty_x ty_g;
       assignment g x ty_x;
       dv := g ::!dv)
    
let switchs a args ty_e l = 
  List.iter 
    (fun (sa, t) -> 
       atoms args sa; 
       let ty = term args t in
       unify ty ty_e;
       assignment a t ty) l

let updates args = 
  List.iter 
    (fun {up_arr=a; up_arg=j; up_swts=swts} -> 
       if Hstring.list_mem j args then error (ClashParam j);
       let args_a, ty_a = 
	 try Smt.Typing.find a with Not_found -> error (UnknownArray a)
       in       
       if args_a = [] then error (MustBeAnArray a);
       switchs a (j::args) ([], ty_a) swts) 

let transitions = 
  List.iter 
    (fun ({tr_args = args} as t) -> 
       unique (fun x-> error (DuplicateName x)) args; 
       atoms args t.tr_reqs;
       List.iter 
	 (fun (x, cnf) -> 
	    List.iter (atoms (x::args)) cnf)  t.tr_ureq;
       updates args t.tr_upds;
       assigns args t.tr_assigns;
       nondets t.tr_nondets)

let init_global_env s = 
  List.iter Smt.Typing.declare_type s.type_defs;
  let l = ref [] in
  List.iter 
    (fun (n, t) -> 
       Smt.Typing.declare_name n [] t;
       l := (n, t)::!l) s.consts;
  List.iter 
    (fun (n, t) -> 
       Smt.Typing.declare_name n [] t;
       l := (n, t)::!l) s.globals;
  List.iter 
    (fun (n, (arg, ret)) -> 
       Smt.Typing.declare_name n [arg] ret;
       l := (n, ret)::!l) s.arrays;
  !l

let init_proc () = 
  List.iter 
    (fun n -> Smt.Typing.declare_name n [] Smt.Typing.type_proc) proc_vars

let system s = 
  let l = init_global_env s in
  init s.init;
  Smt.Typing.Variant.init l;
  List.iter unsafe s.unsafe;
  transitions s.trans;
  Smt.Typing.Variant.close ();
  if Options.debug then Smt.Typing.Variant.print ();
  List.map (fun un ->
    let args, p = un in
    let arru = ArrayAtom.of_satom p in
    { 
      t_from = [];
      t_init = s.init;
      t_invs = s.invs;
      t_unsafe = un;
      t_real = un;
      t_arru = arru;
      t_alpha = ArrayAtom.alpha arru args;
      t_trans = s.trans;
      t_deleted = false;
      t_nb = 0;
      t_nb_father = -1;
      t_abstract_signature = STerm.empty;
    }
  ) s.unsafe
