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
(*open Pervasives*)

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
      
exception Error of error * loc

let print_htype fmt (args, ty) =
  fprintf fmt "%a%a" 
    (fun fmt -> List.iter (fprintf fmt "%a -> " Hstring.print)) args
    Hstring.print ty

let print_missing_fields fmt fields =
  fprintf fmt "%a"
    (fun fmt -> List.iter (fprintf fmt " %a " Hstring.print)) fields
       
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
    in
    let ref_ty, ref_cs =
      try Hstring.H.find refinements h1 with Not_found -> [], [] in
    match x2 with
      | Elem (e2, Constr) -> Hstring.H.add refinements h1 (e2::ref_ty, ref_cs)
      | Elem (e2, Glob) -> Hstring.H.add refinements h1 (ref_ty, e2::ref_cs)
      | _ -> ()
  with Exit -> ()

let refinement_cycles () = (* TODO *) ()

let rec term loc args t =
  match t with 
  | Const cs -> 
      let c, _ = MConst.choose cs in
      (match c with
      | ConstInt _ -> t, ([], Smt.Type.type_int)
      | ConstReal _ -> t, ([], Smt.Type.type_real)
      | ConstName x -> 
	      try t, Smt.Symbol.type_of x 
        with Not_found -> error (UnknownName x) loc)
  | Elem (e, Var) -> 
      if Hstring.list_mem e args then t,([], Smt.Type.type_proc)
      else begin 
        try t, Smt.Symbol.type_of e 
        with Not_found -> error (UnknownName e) loc
      end
  | Elem (e, _) ->  t, Smt.Symbol.type_of e
  | Arith (x, _) ->
      begin
	      let _, (args, tx) = term loc args x in
	      if not (Hstring.equal tx Smt.Type.type_int) 
	      && not (Hstring.equal tx Smt.Type.type_real) then 
	      error (MustBeNum x) loc;
	      t, (args, tx)
      end
  | Access(a, li) -> 
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
      t,([], ty_a)
  | Poly(cs, ts) -> failwith "todo"

let rec assignment ?(init_variant=false) g x (_, ty) =
  (*Format.eprintf "GG: %a; x : %a; ty: %a@." Hstring.print g Types.Term.print x Hstring.print ty;*)
  if ty = Smt.Type.type_proc 
     || ty = Smt.Type.type_bool
       || ty = Smt.Type.type_int
  then ()
  else
    match x with
      | Elem (n, Constr) -> 
	  Smt.Variant.assign_constr g n
      | Elem (n, _) | Access (n, _) ->
	  Smt.Variant.assign_var g n;
	  if init_variant then 
	    Smt.Variant.assign_var n g
      | _ -> ()

let atom loc init_variant args a =
  match a with 
    | True | False -> a
    | Comp (Elem(g, Glob) as x, Eq, y)
    | Comp (y, Eq, (Elem(g, Glob) as x))
    | Comp (y, Eq, (Access(g, _) as x))
    | Comp (Access(g, _) as x, Eq, y) ->
      let x', tx = term loc args x in
      let y',ty = term loc args y in
      unify loc tx ty;
      if init_variant then assignment ~init_variant g y' ty;
      Comp(x', Eq, y')
    | Comp (x, op, y) ->
      let x', tx = term loc args x in
      let y',ty = term loc args y in
      unify loc tx ty;
      Comp (x', op, y')
    | Ite _ -> assert false

let atoms loc ?(init_variant=false) args =
  SAtom.map (atom loc init_variant args)

let init (loc, args, lsa) = loc,args, List.map (atoms loc ~init_variant:true args) lsa
 
let unsafe (loc, args, sa) = 
  unique (fun x-> error (DuplicateName x) loc) args; 
  (loc, args, atoms loc args sa)

let nondets loc l = 
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


let assigns args la =
  let dv = ref [] in
  List.map 
    (fun (g, gu, loc) ->
       if Hstring.list_mem g !dv then error (DuplicateAssign g) loc;
       let ty_g = 
	 try Smt.Symbol.type_of g
         with Not_found -> error (UnknownGlobal g) loc in
       let gu = 
         match gu with
           | UTerm x->
             let tx, ty_x = term loc args x in	     
             unify loc ty_x ty_g;
             assignment g tx ty_x;
	     UTerm tx
           | UCase swts ->
             let swts =
	       List.map (fun (sa, t) ->
		 let sa = atoms loc args sa in 
		 let tx, ty_x = term loc args t in
		 unify loc ty_x ty_g;
		 assignment g tx ty_x;
		 sa, tx
               ) swts
	     in UCase swts
       in
       dv := g ::!dv;
    g,gu,loc) la
    
let switchs loc a args ty_e l = 
  List.map 
    (fun (sa, t) -> 
      let sa =  atoms loc args sa in
      let tt,ty = term loc args t in
      unify loc ty ty_e;

      assignment a tt ty;
      sa, tt) l


let updates args upds =
  let dv = ref [] in
  List.map 
    (fun ({up_loc=loc; up_arr=a; up_arg=lj; up_swts=swts} as upd) -> 
       if Hstring.list_mem a !dv then error (DuplicateUpdate a) loc;
       List.iter (fun j -> 
         if Hstring.list_mem j args then error (ClashParam j)loc) lj;
       let args_a, ty_a = 
	 try Smt.Symbol.type_of a with Not_found -> error (UnknownArray a) loc
       in       
       if args_a = [] then error (MustBeAnArray a) loc;
       dv := a ::!dv;
       let up_swts = switchs loc a (lj @ args) ([], ty_a) swts in
       {upd with up_swts}
    ) upds 

    
let check_lets loc args l =
  List.map 
    (fun (x, t) ->  let tt,_ = term loc args t in x, tt) l
	       
let transitions tl = 
  List.map 
    (fun tr -> 
      unique (fun x -> error (DuplicateName x) tr.tr_loc) tr.tr_args;
      let reqs, loc_reqs = tr.tr_reqs in
      let tr_reqs = atoms loc_reqs tr.tr_args reqs, loc_reqs in 
      let tr_ureq =
	List.map 
	 (fun (ur, dnf, loc_req) -> 
	   let dnf =
	     List.map (atoms tr.tr_loc (ur::tr.tr_args)) dnf in
	   ur, dnf, loc_req) tr.tr_ureq in
      let tr_lets = check_lets tr.tr_loc tr.tr_args tr.tr_lets in 
      let tr_upds = updates tr.tr_args tr.tr_upds in 
      let tr_assigns = assigns tr.tr_args tr.tr_assigns in 
      nondets tr.tr_loc tr.tr_nondets;
      { tr with tr_reqs; tr_ureq; tr_lets; tr_upds; tr_assigns }

    ) tl
    

let declare_type (loc, (x, y)) =
  try Smt.Type.declare_enum x y
  with Smt.Error e -> error (Smt e) loc

let declare_t = function
  | Constructors (loc, (x,y)) -> declare_type (loc,(x,y))

let declare_symbol loc n args ret =
  try Smt.Symbol.declare n args ret
  with Smt.Error e -> error (Smt e) loc

let declare_array loc n args ret =
  declare_symbol loc n args ret


let init_global_env s = 
  List.iter declare_t s.type_defs;
  (* patch completeness on Boolean *)
  (*let mybool = Hstring.make "mbool" in
  let mytrue = Hstring.make "@MTrue" in
  let myfalse = Hstring.make "@MFalse" in
  let dummypos = Lexing.dummy_pos, Lexing.dummy_pos in
  declare_type (dummypos, (mybool, [mytrue; myfalse]));*)
  let l = ref [] in
  List.iter 
    (fun (loc, n, t) -> 
       declare_symbol loc n [] t;
       l := (n, t)::!l) s.consts;
  List.iter 
    (fun (loc, n, t) -> 
       declare_symbol loc n [] t;
       l := (n, t)::!l) s.globals;
  List.iter 
    (fun (loc, n, (args, ret)) -> 
       declare_symbol loc n args ret;
      l := (n, ret)::!l) s.arrays;
  
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


let create_node_rename kind vars sa =
  let sigma = Variable.build_subst vars Variable.procs in
  let c = Cube.subst sigma (Cube.create vars sa) in
  (*let c = Cube.create c.vars (Prover.normalize c.litterals) in*)
  let c = Cube.normal_form c in
  Node.create ~kind c


let fresh_args ({ tr_args = args; tr_upds = upds} as tr) = 
  if args = [] then tr
  else
    let sigma = Variable.build_subst args Variable.freshs in
    { tr with 
	tr_args = List.map (Variable.subst sigma) tr.tr_args; 
	tr_reqs = (SAtom.subst sigma (fst tr.tr_reqs), snd tr.tr_reqs) ;
	tr_ureq = 
	List.map 
	  (fun (s, dnf, loc) -> s, List.map (SAtom.subst sigma) dnf, loc) tr.tr_ureq;
	tr_assigns = 
	  List.map (function
            | x, UTerm t, loc -> x, UTerm (Term.subst sigma t),loc
	    | x, UCase swts, loc ->
              let swts = 
	        List.map 
		  (fun (sa, t) ->
                    SAtom.subst sigma sa, Term.subst sigma t) swts in
              x, UCase swts, loc
	  ) tr.tr_assigns;
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
  let s_init = if not Options.notyping then init s.init else s.init in
  (*List.iter (fun (f,t) -> Format.eprintf "system: f: %a; t: %a @." Hstring.print f Hstring.print t) l;*)
  if Options.subtyping  then Smt.Variant.init l;
  let s_unsafe = if not Options.notyping then List.map unsafe s.unsafe else s.unsafe in
  let s_invs = if not Options.notyping then List.map unsafe (List.rev s.invs) else s.invs in
  let s_trans = if not Options.notyping then transitions s.trans else s.trans in
  if Options.(subtyping && not murphi) then begin
    Smt.Variant.close ();
    if Options.debug then Smt.Variant.print ();
  end;

  let init_woloc = let _,v,i = s_init in v,i in
  let invs_woloc =
    List.map (fun (_,v,i) -> create_node_rename Inv v i) s_invs in
  let unsafe_woloc =
    List.map (fun (_,v,u) -> create_node_rename Orig v u) s_unsafe in
  let init_instances = create_init_instances init_woloc invs_woloc in
    if Options.debug && Options.verbose > 0 then
      debug_init_instances init_instances;
 
  { 
    t_globals = List.map (fun (_,g,_) -> g) s.globals;
    t_consts = List.map (fun (_,c,_) -> c) s.consts;
    t_arrays = List.map (fun (_,a,_) -> a) s.arrays;
    t_init = init_woloc;
    t_init_instances = init_instances;
    t_invs = invs_woloc;
    t_unsafe = unsafe_woloc;
    t_trans = List.map add_tau s_trans;
  }
