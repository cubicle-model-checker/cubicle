(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Options
open Format
open Why_ptree
open Common

module S = Set.Make(String)
module Sy = Symbols.Set

module MString = 
  Map.Make(struct type t = string let compare = Pervasives.compare end)

module Types = struct

  (* environment for user-defined types *)
  type t = {
    to_ty : Ty.t MString.t;
    from_labels : string MString.t
  }

  let empty = { to_ty = MString.empty; from_labels = MString.empty }

  let fresh_vars env vars loc =
    let vars, env = 
      List.fold_left 
	(fun (vars, env) x -> 
	   if MString.mem x env.to_ty then error (TypeDuplicateVar x) loc;
	   let nv = Ty.Tvar (Ty.fresh_var ()) in
	   nv::vars, { env with to_ty = MString.add x nv env.to_ty} )
	([], env) vars
    in 
    List.rev vars, env

  let check_number_args loc lty ty = 
    match ty with
      | Ty.Text (lty', s) | Ty.Trecord {Ty.args=lty'; name=s} ->
	  if List.length lty <> List.length lty' then
	    error (WrongNumberofArgs (Hstring.view s)) loc;
	  lty'
      | Ty.Tsum (s, _) -> 
	  if List.length lty <> 0 then
	    error (WrongNumberofArgs (Hstring.view s)) loc;
	  []
      | _ -> assert false

  let equal_pp_vars lpp lvars = 
    try
      List.for_all2 
	(fun pp x -> 
	   match pp with PPTvarid (y, _) -> x = y | _ -> false) lpp lvars
    with Invalid_argument _ -> false

  let rec ty_of_pp loc env rectype = function
    | PPTint -> Ty.Tint
    | PPTbool -> Ty.Tbool
    | PPTunit -> Ty.Tunit
    | PPTreal -> Ty.Treal
    | PPTbitv n -> Ty.Tbitv n
    | PPTvarid (s, _) -> 
	(try MString.find s env.to_ty 
	 with Not_found -> error (UnboundedVar s) loc)
    | PPTexternal (l, s, loc) when s = "farray" ->
	let t1,t2 = match l with
          | [t2] -> PPTint,t2
          | [t1;t2] -> t1,t2
          | _ -> error (WrongArity(s,2)) loc in
	let ty1 = ty_of_pp loc env rectype t1 in
        let ty2 = ty_of_pp loc env rectype t2 in
	Ty.Tfarray (ty1, ty2)
    | PPTexternal (l, s, loc) ->
	begin
	  match rectype with
	    | Some (id, vars, ty) when s = id &&  equal_pp_vars l vars -> ty
	    | _ -> 
		try 
		  let lty = List.map (ty_of_pp loc env rectype) l in
		  let ty = MString.find s env.to_ty in
		  let vars = check_number_args loc lty ty in
		  Ty.instantiate vars lty ty
		with Not_found -> 
		  error (UnknownType s) loc
	end

  let add env vars id body loc = 
    if MString.mem id env.to_ty then error (ClashType id) loc;
    let ty_vars, nenv = fresh_vars env vars loc in
    match body with
      | Abstract -> 
	  { env with to_ty = MString.add id (Ty.text ty_vars id) env.to_ty }
      | Enum lc -> 
	  { env with to_ty = MString.add id (Ty.tsum id lc) env.to_ty }
      | Record lbs -> 
	  let lbs = 
	    List.map (fun (x, pp) -> x, ty_of_pp loc nenv None pp) lbs in
	  { to_ty = MString.add id (Ty.trecord ty_vars id lbs) env.to_ty;
	    from_labels = 
	      List.fold_left 
		(fun fl (l,_) -> MString.add l id fl) env.from_labels lbs
	  }

	  (* hack for recursive records : to be completed *)
	  (*let nenv = 
	    { nenv with 
		to_ty = MString.add id (Ty.text ty_vars id) nenv.to_ty } in
	  let nv = Ty.Tvar (Ty.fresh_var ()) in
	  let lbs = 
	    List.map 
	      (fun (x, pp) -> 
		 x, ty_of_pp loc nenv (Some (id, vars, nv)) pp) lbs 
	  in
	  Ty.unify nv (Ty.trecord ty_vars id lbs);
	  { to_ty = MString.add id (Ty.shorten nv) env.to_ty;
	    from_labels = 
	      List.fold_left 
		(fun fl (l,_) -> MString.add l id fl) env.from_labels lbs
	  }*)

  module SH = Set.Make(Hstring)

  let check_labels lbs ty loc = 
    let rec check_duplicates s = function
      | [] -> ()
      | (lb, _) :: l -> 
	  if SH.mem lb s then error (DuplicateLabel lb) loc;
	  check_duplicates (SH.add lb s) l
    in
    check_duplicates SH.empty lbs;
    match ty with
      | Ty.Trecord {Ty.lbs=l} ->
	  if List.length lbs <> List.length l then 
	    error WrongNumberOfLabels loc;
	  List.iter 
	    (fun (lb, _) -> 
	       try ignore (Hstring.list_assoc lb l) 
	       with Not_found -> error (WrongLabel(lb, ty)) loc) lbs;
	  ty
      | _ -> assert false


  let from_labels env lbs loc = 
    match lbs with
      | [] -> assert false
      | (l, _) :: _ -> 
	  try 
	    let l = Hstring.view l in
	    let ty = MString.find (MString.find l env.from_labels) env.to_ty in
	    check_labels lbs ty loc
	  with Not_found -> error (NoRecordType l) loc

  let rec monomorphized env = function
    | PPTvarid (x, _) when not (MString.mem x env.to_ty) -> 
	{ env with to_ty = MString.add x (Ty.fresh_empty_text ()) env.to_ty } 
    | PPTexternal (args, _, _) ->
	List.fold_left monomorphized env args
    | pp_ty -> env

  let rec rename_vars env = function
    | PPTvarid (x, _) when not (MString.mem x env.to_ty) -> 
	{ env with 
	    to_ty = MString.add x (Ty.Tvar (Ty.fresh_var ())) env.to_ty } 
    | PPTexternal (args, _, _) ->
	List.fold_left rename_vars env args
    | pp_ty -> env

  let init_labels fl id loc = function
    | Record lbs ->
	List.fold_left 
	  (fun fl (s, _) -> 
	     if MString.mem s fl then 
	       error (ClashLabel (s, (MString.find s fl))) loc;
	     MString.add s id fl) fl lbs
    | _ -> fl

end

module Env = struct

  type profile = { args : Ty.t list; result : Ty.t }

  type t = { 
    var_map : (Symbols.t * Ty.t) MString.t ; (* variables' map*)
    types : Types.t ; 
    logics : (Symbols.t * profile) MString.t (* logic symbols' map *)
  }

  let empty = { 
    var_map = MString.empty;  
    types = Types.empty;
    logics = MString.empty
  }

  let add env lv fvar ty = 
    let vmap = 
      List.fold_left 
	(fun vmap x -> MString.add x (fvar x, ty) vmap) env.var_map lv in
    { env with var_map = vmap }

  let add_var env lv pp_ty loc  = 
    let env = { env with types = Types.rename_vars env.types pp_ty } in
    let ty = Types.ty_of_pp loc env.types None pp_ty in
    add env lv Symbols.var ty

  let add_names env lv pp_ty loc = 
    let env = { env with types = Types.monomorphized env.types pp_ty } in
    let ty = Types.ty_of_pp loc env.types None pp_ty in
    add env lv Symbols.name ty

  let add_logics env ac names pp_profile loc = 
    let profile = 
      match pp_profile with
	| PPredicate args -> 
	    let types = List.fold_left Types.rename_vars env.types args in
	    { args = List.map (Types.ty_of_pp loc types None) args; 
	      result = Ty.Tbool }
	| PFunction ([], PPTvarid (_, loc)) -> 
	    error CannotGeneralize loc
	| PFunction(args, res) -> 
	    let types = List.fold_left Types.rename_vars env.types args in
	    let types = Types.rename_vars types res in
	    let args = List.map (Types.ty_of_pp loc types None) args in
	    let res = Types.ty_of_pp loc types None res in
	    { args = args; result = res }
    in
    let logics = 
      List.fold_left 
	(fun logics n -> 
	   let sy = Symbols.name n ~kind:ac in
	   if MString.mem n logics then error (SymbAlreadyDefined n) loc;
	   MString.add n (sy, profile) logics)
	env.logics names
    in
    { env with logics = logics }

  let find {var_map=m} n = MString.find n m

  let mem n {var_map=m} = MString.mem n m

  let list_of {var_map=m} = MString.fold (fun _ c acc -> c::acc) m []

  let add_type_decl env vars id body loc =  
    { env with types = Types.add env.types vars id body loc }

  (* returns a type with fresh variables *)
  let fresh_type env n loc = 
    try
      let s, { args = args; result = r} = MString.find n env.logics in 
      let args, subst = Ty.fresh_list args Ty.esubst in
      let res, _ = Ty.fresh r subst in
      s, { args = args; result = res }
    with Not_found -> error (SymbUndefined n) loc
      
end

let new_id = let r = ref 0 in fun () -> r := !r+1; !r

let rec freevars_term acc t = match t.c.tt_desc with
  | TTvar x -> Sy.add x acc
  | TTapp (_,lt) -> List.fold_left freevars_term acc lt
  | TTinfix (t1,_,t2) | TTget(t1, t2) -> 
      List.fold_left freevars_term acc [t1; t2]
  | TTset (t1, t2, t3) ->
      List.fold_left freevars_term acc [t1; t2; t3]
  | TTdot (t1, _) -> freevars_term acc t1
  | TTrecord lbs -> 
      List.fold_left (fun acc (_, t) -> freevars_term acc t) acc lbs
  | _ -> acc
      
let freevars_atom a = match a.c with
  | TAeq lt | TAneq lt | TAle lt
  | TAlt lt | TAbuilt(_,lt) | TAdistinct lt ->
      List.fold_left freevars_term Sy.empty lt
  | TApred t -> freevars_term  Sy.empty t
  | _ -> Sy.empty
      
let rec freevars_form f = match f with
  | TFatom a -> freevars_atom a
  | TFop (_,lf) ->
      List.fold_left Sy.union Sy.empty 
	(List.map (fun f -> freevars_form f.c) lf)
  | TFforall qf | TFexists qf -> 
      let s = freevars_form qf.qf_form.c in
      List.fold_left (fun acc (s,_) -> Sy.remove s acc) s qf.qf_bvars
  | TFlet(up,v,t,f) -> freevars_term (Sy.remove v (freevars_form f.c)) t
  | TFnamed(_, f) -> freevars_form f.c

let symbol_of = function
    PPadd -> Symbols.Op Symbols.Plus
  | PPsub -> Symbols.Op Symbols.Minus
  | PPmul -> Symbols.Op Symbols.Mult
  | PPdiv -> Symbols.Op Symbols.Div
  | PPmod ->  Symbols.Op Symbols.Modulo
  | _ -> assert false  

let rec type_term env f = 
  let e,t = type_term_desc env f.pp_loc f.pp_desc in
  {c = { tt_desc = e ; tt_ty = t }; annot = new_id ()}

and type_term_desc env loc = function
  | PPconst ConstTrue -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Const type %a@." Ty.print Ty.Tbool;
      TTconst Ttrue, Ty.Tbool
  | PPconst ConstFalse -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Const type %a@." Ty.print Ty.Tbool;
      TTconst Tfalse, Ty.Tbool
  | PPconst ConstVoid -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Const type %a@." Ty.print Ty.Tunit;
      TTconst Tvoid, Ty.Tunit
  | PPconst (ConstInt n) -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Const type %a@." Ty.print Ty.Tint;
      TTconst(Tint n), Ty.Tint
  | PPconst (ConstReal n) -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Const type %a@." Ty.print Ty.Treal;
      TTconst(Treal n), Ty.Treal
  | PPconst (ConstBitv n) -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Const type %a@." Ty.print 
      (Ty.Tbitv (String.length n));
      TTconst(Tbitv n), Ty.Tbitv (String.length n)
  | PPvar p -> 
      begin
	try let s,t = Env.find env p in 
	    if qualif = 1 then
	      fprintf fmt "[rule] TR-Typing-Var$_\\Gamma$ type %a@."
		Ty.print t;
	    TTvar s , t
	with Not_found -> 
	  match Env.fresh_type env p loc with
	    | s, { Env.args = []; result = ty} -> 
	      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Var$_\\Delta$ type %a@." 
		Ty.print ty;
	      TTvar s , ty 
	    | _ -> error (ShouldBeApply p) loc
      end
  | PPapp(p,args) -> 
      begin
	let te_args = List.map (type_term env) args in
	let lt_args =  List.map (fun {c={tt_ty=t}} -> t) te_args in
	let s, {Env.args = lt; result = t} = Env.fresh_type env p loc in
	try
	  List.iter2 Ty.unify lt lt_args; 
	  if qualif = 1 then fprintf fmt "[rule] TR-Typing-App type %a@." Ty.print t;
	  TTapp(s,te_args), t
	with 
	  | Ty.TypeClash(t1,t2) -> 
	      error (Unification(t1,t2)) loc
	  | Invalid_argument _ -> 
	      error (WrongNumberofArgs p) loc
      end
  | PPinfix(t1,(PPadd | PPsub | PPmul | PPdiv as op),t2) ->
      begin
	let s = symbol_of op in
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	let ty2 = Ty.shorten te2.c.tt_ty in
	match ty1, ty2 with
	  | Ty.Tint, Ty.Tint -> 
	    if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpBin type %a@."
	      Ty.print ty1;
	    TTinfix(te1,s,te2) , ty1
	  | Ty.Treal, Ty.Treal -> 
	    if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpBin type %a@."
	      Ty.print ty2; 
	    TTinfix(te1,s,te2), ty2
	  | Ty.Tint, _ -> error (ShouldHaveType(ty2,Ty.Tint)) t2.pp_loc
	  | Ty.Treal, _ -> error (ShouldHaveType(ty2,Ty.Treal)) t2.pp_loc
	  | _ -> error (ShouldHaveTypeIntorReal ty1) t1.pp_loc
      end
  | PPinfix(t1, PPmod, t2) ->
      begin
	let s = symbol_of PPmod in
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	let ty2 = Ty.shorten te2.c.tt_ty in
	match ty1, ty2 with
	  | Ty.Tint, Ty.Tint ->  
	    if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpMod type %a@."
	      Ty.print ty1;
	    TTinfix(te1,s,te2) , ty1
	  | _ -> error (ShouldHaveTypeInt ty1) t1.pp_loc
      end
  | PPprefix(PPneg, {pp_desc=PPconst (ConstInt n)}) -> 
    if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpUnarith type %a@." 
      Ty.print Ty.Tint;
      TTconst(Tint ("-"^n)), Ty.Tint
  | PPprefix(PPneg, {pp_desc=PPconst (ConstReal n)}) -> 
    if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpUnarith type %a@." 
      Ty.print Ty.Treal;
      TTconst(Treal (Num.minus_num n)), Ty.Treal
  | PPprefix(PPneg, e) -> 
      let te = type_term env e in
      let ty = Ty.shorten te.c.tt_ty in
      if ty<>Ty.Tint && ty<>Ty.Treal then
	error (ShouldHaveTypeIntorReal ty) e.pp_loc;
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpUnarith type %a@." 
	Ty.print ty;
      TTprefix(Symbols.Op Symbols.Minus, te), ty
  | PPconcat(t1, t2) ->
      begin
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	let ty2 = Ty.shorten te2.c.tt_ty in
	match ty1, ty2 with
	  | Ty.Tbitv n , Ty.Tbitv m -> 
	    if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpConcat type %a@." 
	      Ty.print (Ty.Tbitv (n+m));
	    TTconcat(te1, te2), Ty.Tbitv (n+m)
	  | Ty.Tbitv _ , _ -> error (ShouldHaveTypeBitv ty2) t2.pp_loc
	  | _ , Ty.Tbitv _ -> error (ShouldHaveTypeBitv ty1) t1.pp_loc
	  | _ -> error (ShouldHaveTypeBitv ty1) t1.pp_loc
      end
  | PPextract(e, ({pp_desc=PPconst(ConstInt i)} as ei),
	      ({pp_desc=PPconst(ConstInt j)} as ej)) ->
      begin
	let te = type_term env e in
	let tye = Ty.shorten te.c.tt_ty in
	let i = int_of_string i in
	let j = int_of_string j in
	match tye with
	  | Ty.Tbitv n -> 
	      if i>j then error (BitvExtract(i,j)) loc;
	      if j>=n then error (BitvExtractRange(n,j) ) loc;
	      let tei = type_term env ei in
	      let tej = type_term env ej in
	      if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpExtract type %a@." 
		Ty.print (Ty.Tbitv (j-i+1));
	      TTextract(te, tei, tej), Ty.Tbitv (j-i+1)
	  | _ -> error (ShouldHaveType(tye,Ty.Tbitv (j+1))) loc
      end
  | PPget (t1, t2) ->
      begin
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let tyarray = Ty.shorten te1.c.tt_ty in
	let tykey2 = Ty.shorten te2.c.tt_ty in
	match tyarray with
	  | Ty.Tfarray (tykey,tyval) ->
	      begin try
	        Ty.unify tykey tykey2;
		if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpGet type %a@." 
		  Ty.print tyval;
                TTget(te1, te2), tyval
	      with
	        | Ty.TypeClash(t1,t2) ->
	            error (Unification(t1,t2)) loc
              end
	  | _ -> error ShouldHaveTypeArray t1.pp_loc
      end
  | PPset (t1, t2, t3) ->
      begin
	let te1 = type_term env t1 in
	let te2 = type_term env t2 in
	let te3 = type_term env t3 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	let tykey2 = Ty.shorten te2.c.tt_ty in
	let tyval2 = Ty.shorten te3.c.tt_ty in
	try
	  match ty1 with
	    | Ty.Tfarray (tykey,tyval) ->
		Ty.unify tykey tykey2;Ty.unify tyval tyval2;
		if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpSet type %a@." 
		  Ty.print ty1;
		TTset(te1, te2, te3), ty1
	    | _ -> error ShouldHaveTypeArray t1.pp_loc
	with
	  | Ty.TypeClash(t, t') -> 
	      error (Unification(t, t')) loc
      end
  | PPif(t1,t2,t3) ->
      begin
	let te1 = type_term env t1 in
	let ty1 = Ty.shorten te1.c.tt_ty in
	if not (Ty.equal ty1 Ty.Tbool) then 
	  error (ShouldHaveType(ty1,Ty.Tbool)) t1.pp_loc;
	let te2 = type_term env t2 in
	let te3 = type_term env t3 in
	let ty2 = Ty.shorten te2.c.tt_ty in
	let ty3 = Ty.shorten te3.c.tt_ty in
	if not (Ty.equal ty2 ty3) then
	  error (ShouldHaveType(ty3,ty2)) t3.pp_loc;
	if qualif = 1 then fprintf fmt "[rule] TR-Typing-Ite type %a@." 
	  Ty.print ty2;
	TTapp(Symbols.name "ite",[te1;te2;te3]) , ty2
      end
  | PPnamed(lbl, t) -> 
      let te = type_term env t in
      te.c.tt_desc, te.c.tt_ty
  | PPdot(t, a) -> 
      begin
	let te = type_term env t in
	let ty = Ty.shorten te.c.tt_ty in
	match ty with
	  | Ty.Trecord {Ty.name=g; lbs=lbs} -> 
	      begin 
		try 
		  let a = Hstring.make a in
		  TTdot(te, a), Hstring.list_assoc a lbs
		with Not_found -> 
		  let g = Hstring.view g in
		  error (ShouldHaveLabel(g,a)) t.pp_loc
	      end
	  | _ -> error (ShouldHaveTypeRecord ty) t.pp_loc
      end
  | PPrecord lbs ->
      begin
	let lbs = 
	  List.map (fun (lb, t) -> Hstring.make lb, type_term env t) lbs in
	let lbs = List.sort 
	  (fun (l1, _) (l2, _) -> Hstring.compare l1 l2) lbs in
	let ty = Types.from_labels env.Env.types lbs loc in
	let ty, _ = Ty.fresh (Ty.shorten ty) Ty.esubst in
	match ty with
	  | Ty.Trecord {Ty.lbs=ty_lbs} ->
	      begin
		try
		  let lbs = 
		    List.map2 
		      (fun (s, te) (lb,ty_lb)-> 
			 Ty.unify te.c.tt_ty ty_lb; 
			 lb, te) lbs ty_lbs
		  in
		  TTrecord(lbs), ty
		with Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) loc
	      end
	  | _ -> error ShouldBeARecord loc
      end
  | PPwith(e, lbs) ->
      begin
	let te = type_term env e in
	let lbs = 
	  List.map 
	    (fun (lb, t) -> Hstring.make lb, (type_term env t, t.pp_loc)) lbs in
	let ty = Ty.shorten te.c.tt_ty in
	match ty with
	  | Ty.Trecord {Ty.lbs=ty_lbs} ->
	      let nlbs = 
		List.map 
		  (fun (lb, ty_lb) -> 
		     try 
		       let v, _ = Hstring.list_assoc lb lbs in
		       Ty.unify ty_lb v.c.tt_ty;
		       lb, v
		     with 
		       | Not_found -> 
			   lb, {c = { tt_desc = TTdot(te, lb); tt_ty = ty_lb}; 
				annot = te.annot }
		       | Ty.TypeClash(t1,t2) -> 
			   error (Unification(t1,t2)) loc
		  ) ty_lbs
	      in
	      List.iter 
		(fun (lb, _) -> 
		   try ignore (Hstring.list_assoc lb ty_lbs)
		   with Not_found -> error (NoLabelInType(lb, ty)) loc) lbs;
	      TTrecord(nlbs), ty
	  | _ ->  error ShouldBeARecord loc
      end
  | PPlet(x, t1, t2) ->
      let te1 = type_term env t1 in
      let ty1 = Ty.shorten te1.c.tt_ty in
      let env = Env.add env [x] Symbols.name ty1 in 
      let te2 = type_term env t2 in
      let ty2 = Ty.shorten te2.c.tt_ty in
      let s, _ = Env.find env x in
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Let type %a@." 
	Ty.print ty2;
      TTlet(s, te1, te2), ty2
  | _ -> error SyntaxError loc

let rec join_forall f = match f.pp_desc with
    PPforall(vs,ty,trs1,f) -> 
      let tyvars,trs2,f = join_forall f in  
      (vs,ty)::tyvars , trs1@trs2 , f
  | PPnamed(lbl, f) -> 
      join_forall f
  | _ -> [] , [] , f

let rec join_exists f = match f.pp_desc with
  | PPexists (vars, ty, f) -> 
      let tyvars,f = join_exists f in  
      (vars, ty)::tyvars ,  f
  | PPnamed (_, f) -> join_exists f
  | _ -> [] , f

let rec type_form env f = 
  let form, vars = match f.pp_desc with
    | PPconst ConstTrue -> 
        if qualif = 1 then fprintf fmt "[rule] TR-Typing-True$_F$@.";
	TFatom {c=TAtrue; annot=new_id ()}, Sy.empty
    | PPconst ConstFalse ->  
        if qualif = 1 then fprintf fmt "[rule] TR-Typing-False$_F$@.";
	TFatom {c=TAfalse; annot=new_id ()}, Sy.empty
    | PPvar p ->
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Var$_F$@.";
	let r = begin
	  match Env.fresh_type env p f.pp_loc with
	    | s, { Env.args = []; result = Ty.Tbool} -> 
		(try 
		   TFatom {c = TAbuilt(Builtin.is_builtin p,[]);
			   annot = new_id() }
		 with Not_found -> 
		   let t2 = {c = {tt_desc=TTconst Ttrue;tt_ty=Ty.Tbool};
			     annot = new_id ()} in
		   let t1 = {c = {tt_desc=TTvar s; tt_ty=Ty.Tbool};
			     annot = new_id ()} in
		   TFatom {c = TAeq [t1;t2]; annot=new_id ()})
	    | _ -> error (NotAPropVar p) f.pp_loc
	end in r, freevars_form r
	  
    | PPapp(p,args ) -> 
        if qualif = 1 then fprintf fmt "[rule] TR-Typing-App$_F$@.";
	let r = 
	  begin
	    let te_args = List.map (type_term env) args in
	    let lt_args =  List.map (fun {c={tt_ty=t}} -> t) te_args in
	    match Env.fresh_type env p f.pp_loc with
	      | s , { Env.args = lt; result = Ty.Tbool} -> 
		  begin
		    try
		      List.iter2 Ty.unify lt lt_args;
		      (try 
			 TFatom { c = TAbuilt(Builtin.is_builtin p,te_args);
				  annot=new_id ()}
		       with Not_found -> 
			 let t1 = { 
			   c = {tt_desc=TTapp(s,te_args); tt_ty=Ty.Tbool};
			   annot=new_id (); } 
			 in
			 TFatom { c = TApred t1; annot=new_id () })
		    with 
		      | Ty.TypeClash(t1,t2) -> 
			  error (Unification(t1,t2)) f.pp_loc
		      | Invalid_argument _ -> 
			  error (WrongNumberofArgs p) f.pp_loc
		  end
	      | _ -> error (NotAPredicate p) f.pp_loc
	  end 
	in r, freevars_form r
	  
    | PPdistinct (args) ->
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Distinct$_F$@.";
	let r = 
	  begin
	    let te_args = List.map (type_term env) args in
	    let lt_args =  List.map (fun {c={tt_ty=t}} -> t) te_args in
	    try
	      let t = match lt_args with
		| t::_ -> t
		| [] ->
		    error (WrongNumberofArgs "distinct") f.pp_loc
	      in
	      List.iter (Ty.unify t) lt_args; 
	      TFatom { c = TAdistinct te_args; annot=new_id () }
	    with 
	      | Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
	  end
	in r, freevars_form r

    | PPinfix 
	({pp_desc = PPinfix (_, (PPlt|PPle|PPgt|PPge|PPeq|PPneq), a)} as p, 
	 (PPlt | PPle | PPgt | PPge | PPeq | PPneq as r), b) ->
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpComp$_F$@.";
	let r = 
          let q = { pp_desc = PPinfix (a, r, b); pp_loc = f.pp_loc } in
          let f1,_ = type_form env p in
          let f2,_ = type_form env q in
          TFop(OPand, [f1;f2])
	in r, freevars_form r
    | PPinfix(t1, (PPeq | PPneq as op), t2) -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpBin$_F$@.";
	let r = 
	  let tt1 = type_term env t1 in
	  let tt2 = type_term env t2 in
	  try
	    Ty.unify tt1.c.tt_ty tt2.c.tt_ty;
	    match op with
	      | PPeq -> TFatom {c = TAeq [tt1; tt2]; annot = new_id()}
	      | PPneq -> TFatom {c = TAneq [tt1; tt2]; annot = new_id()}
	      | _ -> assert false
	  with Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
	in r, freevars_form r
    | PPinfix(t1, (PPlt | PPgt | PPge | PPle as op), t2) -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpComp$_F$@.";
	let r = 
	  let tt1 = type_term env t1 in
	  let tt2 = type_term env t2 in
	  try
	    Ty.unify tt1.c.tt_ty tt2.c.tt_ty;
	    let ty = Ty.shorten tt1.c.tt_ty in 
	    match ty with
	      | Ty.Tint | Ty.Treal -> 
		  let top = 
		    match op with
		      | PPlt -> TAlt [tt1; tt2]
		      | PPgt -> TAlt [tt2; tt1]
		      | PPle -> TAle [tt1; tt2]
		      | PPge -> TAle [tt2; tt1]
		      | PPeq -> TAeq [tt1; tt2]
		      | PPneq -> TAneq [tt1; tt2]
		      | _ -> assert false
		  in
		  TFatom {c = top; annot=new_id ()}
	      | _ -> error (ShouldHaveTypeIntorReal ty) t1.pp_loc
	  with Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
	in r, freevars_form r
    | PPinfix(f1,op ,f2) -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpConnectors$_F$@.";
	begin
	  let f1,fv1 = type_form env f1 in
	  let f2,fv2 = type_form env f2 in
	  ((match op with
	      | PPand -> 
		  TFop(OPand,[f1;f2])
	      | PPor -> TFop(OPor,[f1;f2])
	      | PPimplies -> TFop(OPimp,[f1;f2])
	      | PPiff -> TFop(OPiff,[f1;f2])
	      | _ -> assert false), Sy.union fv1 fv2)
	end
    | PPprefix(PPnot,f) ->
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-OpNot$_F$@."; 
	let f, fv = type_form env f in TFop(OPnot,[f]),fv
    | PPif(f1,f2,f3) -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Ite$_F$@.";
	let f1 = type_term env f1 in
	let f2,fv2 = type_form env f2 in
	let f3,fv3 = type_form env f3 in
	TFop(OPif f1,[f2;f3]), Sy.union fv2 fv3
    | PPnamed(lbl,f) -> 
	let f, fv = type_form env f in
	let lbl = Hstring.make lbl in
	TFnamed(lbl, f), fv
    | PPforall _ | PPexists _ ->
	let ty_vars, ty, triggers, f' = 
	  match f.pp_desc with 
	    | PPforall(vars,ty,triggers,f') -> 
		let ty_vars, triggers', f' = join_forall f' in
		(vars, ty)::ty_vars,ty ,triggers@triggers', f'
	    | PPexists(vars,ty,f') -> 
		let ty_vars, f' = join_exists f' in
		(vars, ty)::ty_vars, ty, [], f'
	    | _ -> assert false
	in
	let env' = 
	  List.fold_left 
	    (fun env (lv,pp_ty) -> 
	       Env.add_var env lv pp_ty f.pp_loc) env ty_vars in
	let f', fv = type_form env' f' in
	let ty_triggers = List.map (List.map (type_term env')) triggers in
	let upbvars = Env.list_of env in
	let bvars = 
	  List.fold_left 
	    (fun acc (l,_) -> 
	       let tys = List.map (Env.find env') l in
	       let tys = List.filter (fun (s,_) -> Sy.mem s fv) tys in
	       tys @ acc) [] ty_vars in 
	let qf_form = {
	  qf_upvars = upbvars ; 
	  qf_bvars = bvars ;
	  qf_triggers = ty_triggers ;
	  qf_form = f'}
	in
	(match f.pp_desc with 
	     PPforall _ ->
	       if qualif = 1 then fprintf fmt "[rule] TR-Typing-Forall$_F$@.";
	       TFforall qf_form
	   | _ -> 
	     if qualif = 1 then fprintf fmt "[rule] TR-Typing-Exists$_F$@.";
	     Existantial.make qf_form), 
	(List.fold_left (fun acc (l,_) -> Sy.remove l acc) fv bvars)
    | PPlet (var,t,f) -> 
      if qualif = 1 then fprintf fmt "[rule] TR-Typing-Let$_F$@.";
	let {c= { tt_ty = ttype }} as tt = type_term env t in
	let svar = Symbols.var var in
	let up = Env.list_of env in
	let env = 
	  {env with 
	     Env.var_map = MString.add var (svar, ttype) env.Env.var_map} in
	let f,fv = type_form env f in
	TFlet (up ,svar , tt, f), freevars_term (Sy.remove svar fv) tt
    | _ -> 
	let te1 = type_term env f in
	let ty = te1.c.tt_ty in
	match ty with
	  | Ty.Tbool -> 
	      let te2 = {c = {tt_desc=TTconst Ttrue;tt_ty=Ty.Tbool};
			 annot = new_id ()} 
	      in
	      let r = TFatom {c = TAeq [te1;te2]; annot=new_id ()} in
	      r, freevars_form r
	  | _ -> error ShouldHaveTypeProp f.pp_loc
  in
  {c = form; annot = new_id ()}, vars


let make_rules loc f = match f.c with
  | TFforall {qf_bvars = vars; qf_form = {c = TFatom {c = TAeq [t1; t2]}}} ->
      {rwt_vars = vars; rwt_left = t1; rwt_right = t2}
  | TFatom {c = TAeq [t1; t2]} -> 
      {rwt_vars = []; rwt_left = t1; rwt_right = t2}
  | _ -> error SyntaxError loc


let fresh_var = 
  let cpt = ref 0 in
  fun x -> incr cpt; ("_"^x^(string_of_int !cpt))

let rec alpha_renaming s f =
  { f with pp_desc = alpha_rec s f.pp_desc }
and alpha_rec ((up, m) as s) f = 
  match f with
    | PPvar x ->
	begin 
	  try
	    let y = MString.find x m in
	    PPvar y
	  with Not_found -> f 
	end
    | PPapp(k, l) -> 
	PPapp(k, List.map (alpha_renaming s) l)
    | PPdistinct l -> 
	PPdistinct (List.map (alpha_renaming s) l)
    | PPconst _ -> f
    | PPinfix(f1, op, f2) -> 
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	PPinfix(ff1, op, ff2)
    | PPprefix(op, f1) ->
	PPprefix(op, alpha_renaming s f1)
    | PPget(f1,f2) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	PPget(ff1, ff2)
    | PPset(f1, f2, f3) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	let ff3 = alpha_renaming s f3 in
	PPset(ff1, ff2, ff3)
    | PPextract(f1, f2, f3) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	let ff3 = alpha_renaming s f3 in
	PPextract(ff1, ff2, ff3)
    | PPconcat(f1, f2) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	PPconcat(ff1, ff2)
    | PPif(f1, f2, f3) ->
	let ff1 = alpha_renaming s f1 in
	let ff2 = alpha_renaming s f2 in
	let ff3 = alpha_renaming s f3 in
	PPif(ff1, ff2, ff3)
    | PPnamed(n, f1) ->
	PPnamed(n, alpha_renaming s f1)
    | PPforall(xs, ty, trs, f1) ->
	let xs1, xs2 = List.partition (fun x -> S.mem x up) xs in
	let nv = List.map fresh_var xs1 in
	let m = List.fold_left2 (fun m x nx -> MString.add x nx m) m xs1 nv in
	let xs = nv@xs2 in
	let up = List.fold_left (fun up x -> S.add x up) up xs in
	let s = (up, m) in
	let ff1 = alpha_renaming s f1 in
	let trs = List.map (List.map (alpha_renaming s)) trs in
	PPforall(xs, ty, trs, ff1)
    | PPdot(f1, a) ->
	PPdot(alpha_renaming s f1, a)
    | PPrecord l ->
	PPrecord (List.map (fun (a,e) -> a, alpha_renaming s e) l)
    | PPwith(e, l) ->
	let l = List.map (fun (a,e) -> a, alpha_renaming s e) l in
	PPwith(alpha_renaming s e, l)
    | PPlet(x, f1, f2) ->
	let ff1 = alpha_renaming s f1 in
	let s, x = 
	  if S.mem x up then
	    let nx = fresh_var x in
	    let m = MString.add x nx m in
	    let up = S.add nx up in
	    (up, m), nx
	  else
	    (S.add x up, m), x
	in
	let ff2 = alpha_renaming s f2 in
	PPlet(x, ff1, ff2)
	
    | PPexists(lx, ty, f1) ->
	let s, lx = 
	  List.fold_left
	    (fun (s, lx) x ->
	       if S.mem x up then
		 let nx = fresh_var x in
		 let m = MString.add x nx m in
		 let up = S.add nx up in
		 (up, m), nx :: lx
	       else
		 (S.add x up, m), x :: lx)
	    (s, []) lx
	in
	let ff1 = alpha_renaming s f1 in
	PPexists(lx, ty, ff1)
 
let alpha_renaming = alpha_renaming (S.empty, MString.empty)

let inv_infix = function 
  | PPand -> PPor | PPor -> PPand | _ -> assert false

let rec elim_toplevel_forall env bnot f = 
  (* bnot = true : nombre impaire de not *)
  match f.pp_desc with
    | PPforall (lv, pp_ty, _, f) when bnot-> 
	elim_toplevel_forall (Env.add_names env lv pp_ty f.pp_loc) bnot f

    | PPinfix (f1, PPand, f2) when not bnot -> 
	let env , f1 = elim_toplevel_forall env false f1 in
	let env , f2 = elim_toplevel_forall env false f2 in
	env , { f with pp_desc = PPinfix(f1, PPand , f2)}
	
    | PPinfix (f1, PPor, f2) when bnot -> 
	let env , f1 = elim_toplevel_forall env true f1 in
	let env , f2 = elim_toplevel_forall env true f2 in
        env , { f with pp_desc = PPinfix(f1, PPand , f2)}

    | PPinfix (f1, PPimplies, f2) when bnot -> 
        let env , f1 = elim_toplevel_forall env false f1 in
	let env , f2 = elim_toplevel_forall env true f2 in
	  env , { f with pp_desc = PPinfix(f1,PPand,f2)}
	
    | PPprefix (PPnot, f) -> elim_toplevel_forall env (not bnot) f

    | _ when bnot -> 
	env , { f with pp_desc=PPprefix(PPnot,f)}

    | _  -> env , f


let rec intro_hypothesis env valid_mode f = 
  match f.pp_desc with
    | PPinfix(f1,PPimplies,f2) when valid_mode -> 
	let env, f1 = elim_toplevel_forall env (not valid_mode) f1 in
	let env, axioms , goal = intro_hypothesis env valid_mode f2 in
	env, f1::axioms , goal
    | PPforall(lv, pp_ty, _, f) when valid_mode ->  
	intro_hypothesis (Env.add_names env lv pp_ty f.pp_loc) valid_mode f
    | PPexists(lv, pp_ty, f) when not valid_mode-> 
	intro_hypothesis (Env.add_names env lv pp_ty f.pp_loc) valid_mode f
    | _ -> 
	let env , f = elim_toplevel_forall env valid_mode f in
	env , [] , f

let fresh_axiom_name = 
  let cpt = ref 0 in fun () -> incr cpt; "@H"^(string_of_int !cpt)

let check_duplicate_params l =
  let rec loop l acc =
    match l with
      | [] -> ()
      | (loc,x,_)::rem ->
	  if List.mem x acc then
	    error (ClashParam x) loc
	  else loop rem (x::acc)
  in
  loop l []

let rec make_pred loc trs f = function
    [] ->  f
  | [x,t] ->
      { pp_desc = PPforall([x],t,trs,f) ; pp_loc = loc }
  | (x,t)::l -> 
      { pp_desc = PPforall([x],t,[],(make_pred loc trs f l)) ; 
	pp_loc = loc }

let rec max_terms acc f = 
  match f.pp_desc with
    | PPinfix(f1, ( PPand | PPor | PPimplies | PPiff ), f2) 
    | PPconcat(f1, f2) ->  
	let acc = max_terms acc f1 in
	max_terms acc f2

    | PPforall(_, _, _, _) 
    | PPexists(_, _, _) 
    | PPvar _ 
    | PPlet(_, _, _) 
    | PPinfix(_, _, _) -> raise Exit

    | PPif(f1, f2, f3) ->
	let acc = max_terms acc f1 in
	let acc = max_terms acc f2 in
	max_terms acc f3
    | PPextract(f1, _, _) | PPprefix(_, f1) 
    | PPnamed(_, f1) ->
	max_terms acc f1
    | _ -> f::acc

let max_terms f = try max_terms [] f with Exit -> []

let rec mono_term {c = {tt_ty=tt_ty; tt_desc=tt_desc}; annot = id} = 
  let tt_desc = match tt_desc with
    | TTconst _ | TTvar _ -> 
        tt_desc
    | TTinfix (t1, sy, t2) -> 
        TTinfix(mono_term t1, sy, mono_term t2)
    | TTprefix (sy,t) -> 
        TTprefix(sy, mono_term t)
    | TTapp (sy,tl) -> 
        TTapp (sy, List.map mono_term tl)
    | TTget (t1,t2) ->
        TTget (mono_term t1, mono_term t2)
    | TTset (t1,t2,t3) -> 
        TTset(mono_term t1, mono_term t2, mono_term t3)
    | TTextract (t1,t2,t3) -> 
        TTextract(mono_term t1, mono_term t2, mono_term t3)
    | TTconcat (t1,t2)->
        TTconcat (mono_term t1, mono_term t2)
    | TTdot (t1, a) ->
	TTdot (mono_term t1, a)
    | TTrecord lbs ->
	TTrecord (List.map (fun (x, t) -> x, mono_term t) lbs)
    | TTlet (sy,t1,t2)-> 
        TTlet (sy, mono_term t1, mono_term t2)
  in 
  { c = {tt_ty = Ty.monomorphize tt_ty; tt_desc=tt_desc}; annot = id}
 

let monomorphize_atom tat =
  let c = match tat.c with 
    | TAtrue | TAfalse -> tat.c
    | TAeq tl -> TAeq (List.map mono_term tl)
    | TAneq tl -> TAneq (List.map mono_term tl)
    | TAle tl -> TAle (List.map mono_term tl)
    | TAlt tl -> TAlt (List.map mono_term tl)
    | TAdistinct tl -> TAdistinct (List.map mono_term tl)
    | TApred t -> TApred (mono_term t)
    | TAbuilt (hs, tl) -> TAbuilt(hs, List.map mono_term tl)
  in 
  { tat with c = c }

let rec monomorphize_form tf = 
  let c = match tf.c with
    | TFatom tat -> TFatom (monomorphize_atom tat)
    | TFop (oplogic , tfl) ->
        TFop(oplogic, List.map monomorphize_form tfl)
    | TFforall qf ->
        TFforall
          {qf with
             qf_form = monomorphize_form qf.qf_form;
             qf_triggers = List.map (List.map mono_term) qf.qf_triggers}
    | TFexists qf ->
        TFexists 
          {qf with
             qf_form = monomorphize_form qf.qf_form;
             qf_triggers = List.map (List.map mono_term) qf.qf_triggers}
    | TFlet (l, sy, tt, tf) ->
        TFlet(l,sy, mono_term tt, monomorphize_form tf)
    | TFnamed (hs,tf) ->
        TFnamed(hs, monomorphize_form tf)
  in 
  { tf with c = c }

let axioms_of_rules loc name lf acc env =
  let acc = 
    List.fold_left
      (fun acc (f, _) ->
        let f = Triggers.make false f in
        let name = (Common.fresh_string ()) ^ "_" ^ name in
        let td = {c = TAxiom(loc,name,f); annot = new_id () } in
	(td, env)::acc
      ) acc lf
  in 
  acc, env
      
let type_decl (acc, env) d = 
  try
    match d with
      | Logic (loc, ac, lp, pp_ty) -> 
	if qualif = 1 then fprintf fmt "[rule] TR-Typing-LogicFun$_F$@.";
	  let env' = Env.add_logics env ac lp pp_ty loc in
	  let td = {c = TLogic(loc,lp,pp_ty); annot = new_id () } in
	  (td, env)::acc, env'

      | Axiom(loc,name,f) -> 
	if qualif = 1 then fprintf fmt "[rule] TR-Typing-AxiomDecl$_F$@.";
	  let f, _ = type_form env f in 
	  let f = Triggers.make false f in
	  let td = {c = TAxiom(loc,name,f); annot = new_id () } in
	  (td, env)::acc, env

      | Rewriting(loc, name, lr) -> 
	  let lf = List.map (type_form env) lr in
          if Options.rewriting then
            let rules = List.map (fun (f,_) -> make_rules loc f) lf in
	    let td = {c = TRewriting(loc, name, rules); annot = new_id () } in
	    (td, env)::acc, env
          else
            axioms_of_rules loc name lf acc env


      | Goal(loc,n,f) ->
	if qualif = 1 then fprintf fmt "[rule] TR-Typing-GoalDecl$_F$@.";
	  (*let f = move_up f in*)
	  let f = alpha_renaming f in
	  let env', axioms, goal = 
	    intro_hypothesis env (not (!smtfile or !smt2file or !satmode)) f in
	  let acc =
	    List.fold_left
	      (fun acc f ->
		 let f,_ = type_form env' f in
		 let f = monomorphize_form f in
                 let f = Triggers.make false f in
		 let td = {c = TAxiom(loc, fresh_axiom_name(), f);
			   annot = new_id () } in
		 (td, env')::acc) acc axioms
	  in
	  let goal, _ = type_form env' goal in
          let goal = monomorphize_form goal in
	  let goal = Triggers.make true goal in
	  let td = {c = TGoal(loc, n, goal); annot = new_id () } in
	  (td, env')::acc, env

      | Predicate_def(loc,n,l,e) 
      | Function_def(loc,n,l,_,e) ->
	  check_duplicate_params l;
	  let ty = 
	    let l = List.map (fun (_,_,x) -> x) l in
	    match d with
		Function_def(_,_,_,t,_) -> PFunction(l,t) 
	      | _ -> PPredicate l 
	  in
	  let l = List.map (fun (_,x,t) -> (x,t)) l in

	  let env = Env.add_logics env Symbols.Other [n] ty loc in (* TODO *)

	  let lvar = List.map (fun (x,_) -> {pp_desc=PPvar x;pp_loc=loc}) l in
	  let p = {pp_desc=PPapp(n,lvar) ; pp_loc=loc } in
	  let infix = match d with Function_def _ -> PPeq | _ -> PPiff in
	  let f = { pp_desc = PPinfix(p,infix,e) ; pp_loc = loc } in
	  (* le trigger [[p]] ne permet pas de replier la definition,
	     donc on calcule les termes maximaux de la definition pour
	     laisser une possibilite de replier *)
	  let trs = max_terms e in
	  let f = make_pred loc ([p]::[trs]) f l in
	  let f,_ = type_form env f in
	  let f = Triggers.make false f in
	  let td = 
	    match d with 
	      | Function_def(_,_,_,t,_) ->
		if qualif = 1 then 
		  fprintf fmt "[rule] TR-Typing-LogicFun$_F$@.";
		TFunction_def(loc,n,l,t,f)
	      | _ ->
		if qualif = 1 then
		  fprintf fmt "[rule] TR-Typing-LogicPred$_F$@.";
		TPredicate_def(loc,n,l,f)
	  in
	  let td_a = { c = td; annot=new_id () } in
	  (td_a, env)::acc, env

      | TypeDecl(loc, ls, s, body) -> 
	if qualif = 1 then fprintf fmt "[rule] TR-Typing-TypeDecl$_F$@.";
	  let env1 = Env.add_type_decl env ls s body loc in
	  let td1 =  TTypeDecl(loc, ls, s, body) in
	  let td1_a = { c = td1; annot=new_id () } in
          let tls = List.map (fun s -> PPTvarid (s,loc)) ls in
	  let ty = PFunction([], PPTexternal(tls, s, loc)) in
	  match body with
	    | Enum lc -> 
		let env2 = Env.add_logics env1 Symbols.Constructor lc ty loc in
		let td2 = TLogic(loc, lc, ty) in
		let td2_a = { c = td2; annot=new_id () } in
		(td1_a, env1)::(td2_a,env2)::acc, env2
	    | _ -> (td1_a, env1)::acc, env1

  with Warning(e,loc) -> 
    Loc.report loc; 
    acc, env

let file ld = 
  let ltd, _ = 
    List.fold_left 
      (fun acc d -> type_decl acc d)
      ([], Env.empty) ld
  in
  List.rev ltd

let split_goals l =
  let _, _, ret = 
    List.fold_left
      (fun (ctx, hyp, ret) ( (td, env) as x) -> 
	 match td.c with 
	   | TGoal _ -> ctx, [], (x::(hyp@ctx))::ret
	   | TAxiom (_, s, _) when String.length s > 0 && s.[0] = '@' ->
	       ctx, x::hyp, ret
	   | _ -> x::ctx, hyp, ret) ([],[],[]) l
  in 
  List.rev_map List.rev ret

let term env vars t =
  let vmap = 
    List.fold_left
      (fun m (s,ty)->
	 let str = Symbols.to_string s in
	 MString.add str (s,ty) m
      ) env.Env.var_map vars in
  let env = { env with Env.var_map = vmap } in
  type_term env t

type env = Env.t
