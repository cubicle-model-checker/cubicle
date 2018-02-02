(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Util
open Ast
open Types
open Atom
open Pervasives

type error = 
  | UnknownConstr of Hstring.t
  | UnknownVar of Hstring.t
  | UnknownGlobal of Hstring.t
  | DuplicateAssign of Hstring.t
  | DuplicateName of Hstring.t 
  | DuplicateUpdate of Hstring.t
  | UnknownArray of Hstring.t
  | UnknownName of Hstring.t
  | DuplicateInit of Hstring.t
  | NoMoreThanOneArray
  | ClashParam of Hstring.t
  | MustBeAnArray of Hstring.t
  | MustBeOfType of Hstring.t * Hstring.t
  | MustBeNum of term
  | MustBeOfTypeProc of Hstring.t 
  | IncompatibleType of Hstring.t list * Hstring.t * Hstring.t list * Hstring.t
  | NotATerm of Hstring.t
  | WrongNbArgs of Hstring.t * int
  | Smt of Smt.error
  | ConstantAssign of Hstring.t
  | ConstantUpdate of Hstring.t
  | ConstantWrite of Hstring.t
  | DuplicateWrite of Hstring.t
  | ProcCantReadOtherSC
  | NonArrayMustBeWeak
  | MissingThreadInTrans
  | CantUseFenceInInit
  | CantUseFenceInUnsafe
  (* | CantUseReadInInit *)
  (* | OpInvalidInSC *)
  (* | MustReadWeakVar of Hstring.t *)
  (* | MustWriteWeakVar of Hstring.t *)
  (* | MustBeWeakVar of Hstring.t *)

exception Error of error * loc

module S = Set.Make(Hstring)

module Consts = struct
  let s = ref S.empty
  let add x = s := S.add x !s
  let mem x = S.mem x !s
end

type ct = None | Init | Unsafe | Trans

type context = { c: ct; thr: Hstring.t list }

let dctx = { c = None; thr = [] }
let tctx = { c = Trans; thr = [] }
let ictx = { c = Init; thr = [] }
let uctx = { c = Unsafe; thr = [] }

let print_htype fmt (args, ty) =
  fprintf fmt "%a%a" 
    (fun fmt -> List.iter (fprintf fmt "%a -> " Hstring.print)) args
    Hstring.print ty
       
let report fmt = function
  | UnknownConstr e ->
      fprintf fmt "unknown constructor %a" Hstring.print e
  | DuplicateAssign s ->
      fprintf fmt "duplicate assignment for %a" Hstring.print s
  | DuplicateName e ->
      fprintf fmt "duplicate name for %a" Hstring.print e
  | DuplicateUpdate s ->
      fprintf fmt 
	"duplicate array update for %a (You may want to use a case construct)"
	Hstring.print s
  | UnknownVar x ->
      fprintf fmt "unknown variable %a" Hstring.print x
  | UnknownArray a ->
      fprintf fmt "unknown array %a" Hstring.print a
  | UnknownName s ->
      fprintf fmt "unknown name %a" Hstring.print s
  | UnknownGlobal s ->
      fprintf fmt "unknown global %a" Hstring.print s
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
      fprintf fmt "%a must be of type int or real" Term.print s
  | MustBeOfTypeProc s ->
      fprintf fmt "%a must be of proc" Hstring.print s
  | IncompatibleType (args1, ty1, args2, ty2) ->
      fprintf fmt "types %a and %a are not compatible" 
	print_htype (args1, ty1) print_htype (args2, ty2)
  | NotATerm s -> fprintf fmt "%a is not a term" Hstring.print s
  | WrongNbArgs (a, nb) -> fprintf fmt "%a must have %d arguments" Hstring.print a nb
  | Smt (Smt.DuplicateTypeName s) ->
      fprintf fmt "duplicate type name for %a" Hstring.print s
  | Smt (Smt.DuplicateSymb e) ->
      fprintf fmt "duplicate name for %a" Hstring.print e
  | Smt (Smt.UnknownType s) ->
      fprintf fmt "unknown type %a" Hstring.print s
  | Smt (Smt.UnknownSymb s) ->
      fprintf fmt "unknown symbol %a" Hstring.print s
  | ConstantAssign s ->
      fprintf fmt "can't assign to constant %a" Hstring.print s     
  | ConstantUpdate s ->
      fprintf fmt "can't update constant %a" Hstring.print s          
  | ConstantWrite s ->
      fprintf fmt "can't write to constant %a" Hstring.print s     
  | DuplicateWrite s ->
      fprintf fmt "duplicate write for %a" Hstring.print s
  | ProcCantReadOtherSC ->
      fprintf fmt "a process can't read other process's non-weak array cells"
  | NonArrayMustBeWeak ->
      fprintf fmt "non-array variables must be weak under weak models"
  | MissingThreadInTrans ->
      fprintf fmt "missing memory accessing process in transition parameters (specify with [])"
  | CantUseFenceInInit ->
      fprintf fmt "can't use Fence in init"
  | CantUseFenceInUnsafe ->
      fprintf fmt "can't use Fence in unsafe / invariant"
  (* | CantUseReadInInit ->
   *     fprintf fmt "can't use Read in init" *)
  (* | OpInvalidInSC ->
   *     fprintf fmt "operation is invalid in SC" *)
  (* | MustReadWeakVar s ->
   *     fprintf fmt "must use Read to access weak variable %a" Hstring.print s
   * | MustWriteWeakVar s ->
   *     fprintf fmt "must use Write to assign to weak variable %a" Hstring.print s *)
  (* | MustBeWeakVar s ->
   *     fprintf fmt "%a must be a weak variable" Hstring.print s *)

let error e l = raise (Error (e,l))

let rec unique error = function
  | [] -> ()
  | x :: l -> if Hstring.list_mem x l then error x; unique error l

let unify loc (args_1, ty_1) (args_2, ty_2) =
  if not (Hstring.equal ty_1 ty_2) || Hstring.compare_list args_1 args_2 <> 0
  then error (IncompatibleType (args_1, ty_1, args_2, ty_2)) loc

let refinements = Hstring.H.create 17

let infer_type x1 x2 =
  try
    let h1 = match x1 with
      | Const _ | Arith _ -> raise Exit
      | Elem (h1, _) | Access (h1, _) -> h1
      | Read _ -> failwith "Typing.infer_type Read TODO"
      | Write _ -> failwith "Typing.infer_type Write TODO"
      | Fence _ -> failwith "Typing.infer_type Fence TODO"
    in
    let ref_ty, ref_cs =
      try Hstring.H.find refinements h1 with Not_found -> [], [] in
    match x2 with
      | Elem (e2, Constr) -> Hstring.H.add refinements h1 (e2::ref_ty, ref_cs)
      | Elem (e2, Glob) -> Hstring.H.add refinements h1 (ref_ty, e2::ref_cs)
      | _ -> ()
  with Exit -> ()

let refinement_cycles () = (* TODO *) ()

let ty_access loc args a li =
  let args_a, ty_a =
    try Smt.Symbol.type_of a with Not_found -> error (UnknownArray a) loc in
  if List.length args_a <> List.length li then
    error (WrongNbArgs (a, List.length args_a)) loc
  else
    List.iter (fun i ->
      let ty_i =
	if Hstring.list_mem i args then Smt.Type.type_proc
	else
	  try
	    let ia, tyi = Smt.Symbol.type_of i in
	    if ia <> [] then error (MustBeOfTypeProc i) loc;
	    tyi
	  with Not_found -> error (UnknownName i) loc
      in
      if args_a = [] then error (MustBeAnArray a) loc;
      if not (Hstring.equal ty_i Smt.Type.type_proc) then
	error (MustBeOfTypeProc i) loc;
    ) li;
  [], ty_a

let rec term loc ?(ctx=dctx) args = function
  | Const cs ->
      let c, _ = MConst.choose cs in
      (match c with
	| ConstInt _ -> [], Smt.Type.type_int
	| ConstReal _ -> [], Smt.Type.type_real
	| ConstName x | ConstArray (x, _) -> 
	    try Smt.Symbol.type_of x
            with Not_found -> error (UnknownName x) loc)
  | Elem (e, Var) ->
      if Hstring.list_mem e args then [], Smt.Type.type_proc
      else begin 
	  try Smt.Symbol.type_of e with Not_found ->
           error (UnknownName e) loc
      end
  | Elem (e, _) ->
     (*if Weakmem.is_weak e && not ctx.init then error (MustReadWeakVar e) loc;*)
      Smt.Symbol.type_of e
  | Arith (x, _) ->
      begin
	let args, tx = term loc ~ctx args x in
	if not (Hstring.equal tx Smt.Type.type_int) 
	  && not (Hstring.equal tx Smt.Type.type_real) then 
	  error (MustBeNum x) loc;
	args, tx
      end
  | Access(a, li) ->
     (*if Weakmem.is_weak a && not ctx.init then error (MustReadWeakVar a) loc;*)
      if Options.model <> SC && not (Consts.mem a) && ctx.c = Trans
      then begin
        let ok = match li, ctx.thr with
          | p :: _, _ :: _ -> List.exists (fun t -> Hstring.equal p t) ctx.thr
          | p :: _, [] -> failwith "Typing.ml: missing thread in transition"
          | [], _ -> failwith "Typing.ml: empty argument list" in
        if not ok then error (ProcCantReadOtherSC) loc;
      end;
      ty_access loc args a li

  | Read (p, v, vi) ->
      (* if Options.model = Options.SC then error (OpInvalidInSC) loc; *)
      (* if ctx.c = Init then error (CantUseReadInInit) loc; *)
      (* if not (Weakmem.is_weak v) then error (MustBeWeakVar v) loc; *)
      if not (Hstring.list_mem p args) then
	begin try
	  let pa, typ = Smt.Symbol.type_of p in
	  if pa <> [] || not (Hstring.equal typ Smt.Type.type_proc) then
	    error (MustBeOfTypeProc p) loc
	  with Not_found -> error (UnknownName p) loc
	end;
      begin match vi with
        | [] -> Smt.Symbol.type_of v
        | _ -> ty_access loc args v vi
      end
  | Write (p, v, vi, srl) -> failwith "Typing.term : Write should not be typed"
  | Fence p ->
      (* if Options.model = Options.SC then error (OpInvalidInSC) loc; *)
      if ctx.c = Init then error (CantUseFenceInInit) loc;
      if ctx.c = Unsafe then error (CantUseFenceInUnsafe) loc;
      if not (Hstring.list_mem p args) then
	begin try
	  let pa, typ = Smt.Symbol.type_of p in
	  if pa <> [] || not (Hstring.equal typ Smt.Type.type_proc) then
	    error (MustBeOfTypeProc p) loc
	  with Not_found -> error (UnknownName p) loc
	end;
      [], (Hstring.make "mbool") (*Smt.Type.type_bool*)

let assignment ?(init_variant=false) g x (_, ty) = 
  if ty = Smt.Type.type_proc 
     || ty = Smt.Type.type_bool
     || ty = Smt.Type.type_int
  then ()
  else
    match x with
      | Elem (n, Constr) -> 
	  Smt.Variant.assign_constr g n
      | Elem (n, _) | Access (n, _) | Read (_, n, _) -> 
	  Smt.Variant.assign_var g n;
	  if init_variant then 
	    Smt.Variant.assign_var n g
      | _ -> ()

let atom loc init_variant ?(ctx=dctx) args = function
  | True | False -> ()
  | Comp (Elem(g, Glob) as x, Eq, y)
  | Comp (y, Eq, (Elem(g, Glob) as x))
  | Comp (y, Eq, (Access(g, _) as x))
  | Comp (Access(g, _) as x, Eq, y) -> 
      let ty = term ~ctx loc args y in
      unify loc (term ~ctx loc args x) ty;
      if init_variant then assignment ~init_variant g y ty
  | Comp (x, op, y) -> 
      unify loc (term ~ctx loc args x) (term ~ctx loc args y)
  | Ite _ -> assert false

let atoms loc ?(init_variant=false) ?(ctx=dctx) args =
  SAtom.iter (atom loc init_variant ~ctx args)

let init (loc, args, lsa) =
  List.iter (atoms loc ~init_variant:true ~ctx:ictx args) lsa

let unsafe (loc, name, args, sa) = 
  unique (fun x-> error (DuplicateName x) loc) args; 
  atoms ~ctx:uctx loc args sa

let nondets loc ?(ctx=dctx) l = 
  unique (fun c -> error (DuplicateAssign c) loc) l;
  List.iter 
    (fun g -> 
       try
	 let args_g, ty_g = Smt.Symbol.type_of g in
         if args_g <> [] then error (NotATerm g) loc;
         (* Add all values to the subtype *)
         List.iter (Smt.Variant.assign_constr g) (Smt.Type.constructors ty_g);
	 (* if not (Hstring.equal ty_g Smt.Type.type_proc) then  *)
	 (*   error (MustBeOfTypeProc g) *)
       with Not_found -> error (UnknownGlobal g) loc) l

let assigns loc ?(ctx=dctx) args = 
  let dv = ref [] in
  List.iter 
    (fun (g, gu) ->
       if Consts.mem g then error (ConstantAssign g) loc;
       if Hstring.list_mem g !dv then error (DuplicateAssign g) loc;
       let ty_g = 
	 try Smt.Symbol.type_of g
         with Not_found -> error (UnknownGlobal g) loc in
       begin
	 (* if Weakmem.is_weak g then error (MustWriteWeakVar g) loc; *)
         match gu with
         | UTerm x ->
            let ty_x = term ~ctx loc args x in
            unify loc ty_x ty_g;
            assignment g x ty_x;
         | UCase swts ->
            List.iter (fun (sa, x) ->
              atoms ~ctx loc args sa;
              let ty_x = term ~ctx loc args x in
              unify loc ty_x ty_g;
              assignment g x ty_x;
            ) swts
       end;         
       dv := g ::!dv)

let update_ctxthr sa ctx =
  SAtom.fold (fun a ctx ->
    match a with
    | Comp (Elem (p1, Var), Eq, Elem (p2, Var)) ->
       let thr =
         if List.exists (fun p -> Hstring.equal p p1) ctx.thr
           then p2 :: ctx.thr
         else if List.exists (fun p -> Hstring.equal p p2) ctx.thr
           then p1 :: ctx.thr
         else ctx.thr in
       { ctx with thr = thr }
    | _ -> ctx
  ) sa ctx

let writes loc ?(ctx=dctx) args wl =
  (* if Options.model = Options.SC && wl <> []
   *   then error (OpInvalidInSC) loc; *)
  let dv = ref [] in
  List.iter
    (fun (p, v, vi, gu) ->
       if Consts.mem v then error (ConstantWrite v) loc;
       if Hstring.list_mem v !dv then error (DuplicateWrite v) loc;
       let ty_v =
	 try Smt.Symbol.type_of v
         with Not_found -> error (UnknownGlobal v) loc in
       begin (* check vis match this variable number of procs *)
         (* if not (Weakmem.is_weak v) then error (MustBeWeakVar v) loc; *)
         match gu with
         | UTerm t -> (* check vis are in args *)
            let ty_t = term ~ctx loc args t in
            unify loc ty_t ([], snd ty_v);
            assignment v t ty_t
         | UCase swts -> (* check vis are not in args *)
            List.iter (fun (sa, t) ->
              let ctx = update_ctxthr sa ctx in
              atoms ~ctx loc (vi @ args) sa;
              let ty_t = term ~ctx loc (vi @ args) t in
              unify loc ty_t ([], snd ty_v);
              assignment v t ty_t
            ) swts
       end;
       dv := v ::!dv) wl

let rec list_forall2_short p l1 l2 = match l1, l2 with
  | e1 :: l1, e2 :: l2 -> p e1 e2 && list_forall2_short p l1 l2
  | _ -> true
  
let update_ident v1 vi1 = function
  | Access (v2, vi2) ->
     Hstring.equal v1 v2 && list_forall2_short Hstring.equal vi1 vi2
  | _ -> false
  
let switchs loc ?(ctx=dctx) a args ty_e l =
  List.iter 
    (fun (sa, t) ->
       let ctx = update_ctxthr sa ctx in
       atoms ~ctx loc args sa;
       if not (update_ident a args t) then
         let ty = term ~ctx loc args t in
         unify loc ty ty_e;
         assignment a t ty) l

let updates ?(ctx=dctx) args = 
  let dv = ref [] in
  List.iter 
    (fun {up_loc=loc; up_arr=a; up_arg=lj; up_swts=swts} -> 
       if Consts.mem a then error (ConstantUpdate a) loc;
       if Hstring.list_mem a !dv then error (DuplicateUpdate a) loc;
       List.iter (fun j -> 
         if Hstring.list_mem j args then error (ClashParam j) loc) lj;
       let args_a, ty_a = 
	 try Smt.Symbol.type_of a with Not_found -> error (UnknownArray a) loc
       in       
       if args_a = [] then error (MustBeAnArray a) loc;
       (* if Weakmem.is_weak a then error (MustWriteWeakVar a) loc; *)
       dv := a ::!dv;
       switchs ~ctx loc a (lj @ args) ([], ty_a) swts)

let check_lets loc ?(ctx=dctx) args l =
  List.iter 
    (fun (x, t) ->
     let _ = term ~ctx loc args t in ()
    ) l

let transitions =
  List.iter 
    (fun ({tr_args = args; tr_loc = loc} as t) ->
       (* if Options.model = Options.SC && t.tr_fence <> None
        *   then error (OpInvalidInSC) loc; *)
       if Options.model <> Options.SC && t.tr_thread = None
       then error (MissingThreadInTrans) loc;
       let th = match t.tr_thread with Some t -> [t] | None -> [] in
       let ctx = { tctx with thr = th } in
       unique (fun x-> error (DuplicateName x) loc) args; 
       atoms ~ctx loc args t.tr_reqs;
       List.iter 
	 (fun (x, cnf) -> 
	  List.iter (atoms ~ctx loc (x::args)) cnf)  t.tr_ureq;
       check_lets ~ctx loc args t.tr_lets;
       updates ~ctx args t.tr_upds;
       assigns ~ctx loc args t.tr_assigns;
       writes ~ctx loc args t.tr_writes;
       nondets ~ctx loc t.tr_nondets)

let declare_type (loc, (x, y)) =
  try Smt.Type.declare x y
  with Smt.Error e -> error (Smt e) loc

let declare_symbol loc n args ret =
  try Smt.Symbol.declare n args ret
  with Smt.Error e -> error (Smt e) loc


let init_global_env s = 
  List.iter declare_type s.type_defs;
  (* patch completeness on Boolean *)
  (*let mybool = Hstring.make "mbool" in
  let mytrue = Hstring.make "@MTrue" in
  let myfalse = Hstring.make "@MFalse" in
  let dummypos = Lexing.dummy_pos, Lexing.dummy_pos in
  declare_type (dummypos, (mybool, [mytrue; myfalse]));*)
  let l = ref [] in
  let weak_vars = ref [] in
  List.iter 
    (fun (loc, n, pl, t) -> 
       declare_symbol loc n pl t;
       l := (n, t)::!l;
       Consts.add n) s.consts;
  List.iter 
    (fun (loc, n, t, weak) -> 
       declare_symbol loc n [] t;
       if weak then begin
         if Options.model <> Options.SC then
	   weak_vars := (n, [], t) :: !weak_vars;
       end else begin
         if Options.model <> Options.SC then error (NonArrayMustBeWeak) loc;
       end;
       l := (n, t)::!l) s.globals;
  List.iter 
    (fun (loc, n, (args, ret), weak) -> 
       declare_symbol loc n args ret;
       if weak then begin
         if Options.model <> Options.SC then
	   weak_vars := (n, args, ret) :: !weak_vars;
       end;
       l := (n, ret)::!l) s.arrays;
  if Options.model <> Options.SC then Weakmem.init_weak_env !weak_vars;
  !l


let init_proc () =
  List.iter 
    (fun n -> Smt.Symbol.declare n [] Smt.Type.type_proc) Variable.procs


(* let inv_in_init ivars {cube = {Cube.vars; litterals=lits}} = *)
(*   List.fold_left (fun acc sigma -> *)
(*       SAtom.fold (fun a dnsf -> *)
(*           let na = Atom.neg (Atom.subst sigma a) in *)
(*           SAtom.singleton na :: dnsf *)
(*         ) lits acc *)
(*     ) [] (Variable.all_permutations vars ivars) *)


(* let add_invs hinit invs = *)
(*   Hashtbl.iter (fun nb_procs (cdnsf, cdnaf) -> *)
(*       let pvars = Variable.give_procs nb_procs in *)
(*       let iinstp = *)
(*         List.fold_left (fun (cdnsf, cdnaf) inv -> *)
(*             let dnsf = inv_in_init pvars inv in *)
(*             if dnsf = [] then cdnsf, cdnaf *)
(*             else  *)
(*               let cdnsf = *)
(*                 List.map (fun dnf -> *)
(*                   List.fold_left (fun acc sa -> *)
(*                       List.fold_left (fun acc invsa -> *)
(*                           SAtom.union sa invsa :: acc *)
(*                         ) acc dnsf *)
(*                     ) [] dnf *)
(*                   ) cdnsf in *)
(*               cdnsf, List.rev_map (List.rev_map ArrayAtom.of_satom) cdnsf *)
(*           ) (cdnsf, cdnaf) invs *)
(*       in *)
(*       Hashtbl.replace hinit nb_procs iinstp *)
(*     ) hinit *)


let add_invs hinit invs =
  Hashtbl.iter (fun nb_procs init_inst ->
      let pvars = Variable.give_procs nb_procs in
      let init_invs =
        List.fold_left (fun acc inv ->
            let ainv = Node.array inv in
            let vars_inv = Node.variables inv in
            let d = Variable.all_permutations vars_inv pvars in
            List.fold_left (fun acc sigma ->
                let ai = ArrayAtom.apply_subst sigma ainv in
                ai :: acc
              ) acc d
          ) [] invs
      in
      Hashtbl.replace hinit nb_procs { init_inst with init_invs }
    ) hinit

let mk_init_inst_single sa ar = {
  init_cdnf = [[sa]];
  init_cdnf_a = [[ar]];
  init_invs = [];
  }

let mk_init_inst init_cdnf init_cdnf_a =
  { init_cdnf;
    init_cdnf_a;
    init_invs = [] }

let create_init_instances (iargs, l_init) invs = 
  let init_instances = Hashtbl.create 11 in
  begin
    match l_init with
    | [init] ->
      let sa, cst = SAtom.partition (fun a ->
        List.exists (fun z -> has_var z a) iargs) init in
      let ar0 = ArrayAtom.of_satom cst in
      Hashtbl.add init_instances 0 (mk_init_inst_single cst ar0);
      let cpt = ref 1 in
      ignore (List.fold_left (fun v_acc v ->
        let v_acc = v :: v_acc in
        let vars = List.rev v_acc in
        let si = List.fold_left (fun si sigma ->
          SAtom.union (SAtom.subst sigma sa) si)
          cst (Variable.all_instantiations iargs vars) in
        let ar = ArrayAtom.of_satom si in
        Hashtbl.add init_instances !cpt (mk_init_inst_single si ar);
        incr cpt;
        v_acc) [] Variable.procs)

    | _ ->
      let dnf_sa0, dnf_ar0 =
        List.fold_left (fun (dnf_sa0, dnf_ar0) sa ->
          let sa0 = SAtom.filter (fun a ->
            not (List.exists (fun z -> has_var z a) iargs)) sa in
          let ar0 = ArrayAtom.of_satom sa0 in
          sa0 :: dnf_sa0, ar0 :: dnf_ar0) ([],[]) l_init in
      Hashtbl.add init_instances 0  (mk_init_inst [dnf_sa0] [dnf_ar0]);
      let cpt = ref 1 in
      ignore (List.fold_left (fun v_acc v ->
        let v_acc = v :: v_acc in
        let vars = List.rev v_acc in
        let inst_sa, inst_ar =
          List.fold_left (fun (cdnf_sa, cdnf_ar) sigma ->
            let dnf_sa, dnf_ar = 
              List.fold_left (fun (dnf_sa, dnf_ar) init ->
              let sa = SAtom.subst sigma init in
              try
                let sa = Cube.simplify_atoms sa in
                let ar = ArrayAtom.of_satom sa in
                sa :: dnf_sa, ar :: dnf_ar
              with Exit (* sa = False, don't add this conjunct*) ->
                dnf_sa, dnf_ar
            ) ([],[]) l_init in
            dnf_sa :: cdnf_sa, dnf_ar :: cdnf_ar
          ) ([],[]) (Variable.all_instantiations iargs vars) in
        let inst = mk_init_inst inst_sa inst_ar in
        Hashtbl.add init_instances !cpt inst;
        incr cpt;
        v_acc) [] Variable.procs)
    end;

  (* add user supplied invariants to init *)
  add_invs init_instances invs;
  (* Hashtbl.iter (fun nb (cdnf, _) -> *)
  (*   eprintf "> %d --->@." nb; *)
  (*   List.iter (fun dnf -> *)
  (*       eprintf "[[ %a ]]@." (Pretty.print_list SAtom.print " ||@ ") dnf *)
  (*     ) cdnf; *)
  (*   eprintf "@." *)
  (* ) init_instances; *)
  init_instances


let debug_init_instances insts =
  Hashtbl.iter
    (fun nbp init_inst ->
     Pretty.print_double_line err_formatter ();
     eprintf "%d PROCS :\n" nbp;
     Pretty.print_line err_formatter ();
     List.iter
       (fun dnf ->
        List.iter (eprintf "( %a ) ||@." SAtom.print_inline) dnf;
        eprintf "@.";
       ) init_inst.init_cdnf;
     Pretty.print_double_line err_formatter ();
     eprintf "@.";
    ) insts


let create_node_rename name kind vars sa =
  let sigma = Variable.build_subst vars Variable.procs in
  let c = Cube.subst sigma (Cube.create vars sa) in
  let c = Cube.normal_form c in
  Node.create ~name ~kind c


let fresh_args ({ tr_args = args; tr_upds = upds} as tr) = 
  if args = [] then tr
  else
    let sigma = Variable.build_subst args Variable.freshs in
    { tr with 
	tr_args = List.map (Variable.subst sigma) tr.tr_args; 
	tr_reqs = SAtom.subst sigma tr.tr_reqs;
	tr_ureq = 
	List.map 
	  (fun (s, dnf) -> s, List.map (SAtom.subst sigma) dnf) tr.tr_ureq;
	tr_assigns = 
	  List.map (function
                     | x, UTerm t -> x, UTerm (Term.subst sigma t)
                     | x, UCase swts ->
                        let swts = 
	                  List.map 
		            (fun (sa, t) ->
                             SAtom.subst sigma sa, Term.subst sigma t) swts in
                        x, UCase swts
	           ) tr.tr_assigns;
	tr_writes =
	  List.map (fun (p, v, vi, gu) ->
	    let sp = Variable.subst sigma p in
	    let svi = List.map (Variable.subst sigma) vi in
            let sgu = match gu with
              | UTerm t -> UTerm (Term.subst sigma t)
              | UCase swts -> UCase (List.map (fun (sa, t) ->
                                SAtom.subst sigma sa, Term.subst sigma t) swts)
            in
	    sp, v, svi, sgu
	  ) tr.tr_writes;
	tr_upds = 
	List.map 
	  (fun ({up_swts = swts} as up) -> 
	     let swts = 
	       List.map 
		 (fun (sa, t) -> SAtom.subst sigma sa, Term.subst sigma t) swts
	     in
	     { up with up_swts = swts }) 
	  upds}


let add_tau tr =
  (* (\* let tr = fresh_args tr in *\) *)
  (* { tr with *)
  (*   tr_tau = Pre.make_tau tr } *)
  let pre,reset_memo = Pre.make_tau tr in
  { tr_info = tr;
    tr_tau = pre;
    tr_reset = reset_memo;
  }

let system s = 
  let l = init_global_env s in
  if not Options.notyping then init s.init;
  if Options.subtyping    then Smt.Variant.init l;
  if not Options.notyping then List.iter unsafe s.unsafe;
  if not Options.notyping then List.iter unsafe (List.rev s.invs);
  if not Options.notyping then transitions s.trans;
  if Options.(subtyping && not murphi && solver <> AltErgoFile) then begin
    Smt.Variant.close ();
    if Options.debug then Smt.Variant.print ();
  end;

  let init_woloc = let _,v,i = s.init in v,i in
  let invs_woloc = List.map (fun (_,n,v,i) ->
    create_node_rename n Inv v (Weakpre.remove_reads i)) s.invs in
  let invs_woloc_e = List.map (fun (_,n,v,i) ->
    create_node_rename n Inv v (Weakpre.instantiate_init_evts i)) s.invs in
  let unsafe_woloc_e = List.map (fun (_,n,v,u) ->
    create_node_rename n Orig v (Weakpre.instantiate_init_evts u)) s.unsafe in
  let init_instances = create_init_instances init_woloc invs_woloc in
  if Options.debug && Options.verbose > 0 then
    debug_init_instances init_instances;
  { 
    t_globals = List.map (fun (_,g,_,_) -> g) s.globals;
    t_consts = List.map (fun (_,c,pl,_) -> (c,pl)) s.consts;
    t_arrays = List.map (fun (_,a,_,_) -> a) s.arrays;
    t_init = init_woloc;
    t_init_instances = init_instances;
    t_invs = invs_woloc_e;
    t_unsafe = unsafe_woloc_e;
    t_trans = List.map add_tau s.trans;
  }
