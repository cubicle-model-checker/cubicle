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
open Options
open Util
open Ast
open Types


module T = Smt.Term
module F = Smt.Formula

module SMT = Smt.Make (Options)

let proc_terms =
  List.iter 
    (fun x -> Smt.Symbol.declare x [] Smt.Type.type_proc) Variable.procs;
  List.map (fun x -> T.make_app x []) Variable.procs

let distinct_vars = 
  let t = Array.make max_proc F.f_true in
  let _ = 
    List.fold_left 
      (fun (acc,i) v -> 
	 if i<>0 then t.(i) <- F.make_lit F.Neq (v::acc);
	 v::acc, i+1) 
      ([],0) proc_terms 
  in
  function n -> if n = 0 then F.f_true else t.(n-1)

(* let _ = SMT.assume ~id:0 (distinct_vars max_proc) *)

let order_vars =
  let t = Array.make max_proc F.f_true in
  let _ =
    List.fold_left
      (fun (acc, lf, i) v ->
        match acc with
          | v2::r ->
            let lf = (F.make_lit F.Lt [v2;v]) :: lf in
            t.(i) <- F.make F.And lf;
            v::acc, lf, i+1
          | [] -> v::acc, lf, i+1)
      ([], [], 0) proc_terms
  in
  function n -> if n = 0 then F.f_true else t.(n-1)

let make_op_comp = function
  | Eq -> F.Eq
  | Lt -> F.Lt
  | Le -> F.Le
  | Neq -> F.Neq

let make_const = function
  | ConstInt i -> T.make_int i
  | ConstReal i -> T.make_real i
  | ConstName n -> T.make_app n []

let ty_const = function
  | ConstInt _ -> Smt.Type.type_int
  | ConstReal _ -> Smt.Type.type_real
  | ConstName n -> snd (Smt.Symbol.type_of n)

let rec mult_const tc c i =
 match i with
  | 0 -> 
    if ty_const c = Smt.Type.type_int then T.make_int (Num.Int 0)
    else T.make_real (Num.Int 0)
  | 1 -> tc
  | -1 -> T.make_arith T.Minus (mult_const tc c 0) tc
  | i when i > 0 -> T.make_arith T.Plus (mult_const tc c (i - 1)) tc
  | i when i < 0 -> T.make_arith T.Minus (mult_const tc c (i + 1)) tc
  | _ -> assert false

let make_arith_cs =
  MConst.fold 
    (fun c i acc ->
      let tc = make_const c in
      let tci = mult_const tc c i in
       T.make_arith T.Plus acc tci)

let make_cs cs =
  let c, i = MConst.choose cs in
  let t_c = make_const c in
  let r = MConst.remove c cs in
  if MConst.is_empty r then mult_const t_c c i
  else make_arith_cs r (mult_const t_c c i)
  
	 
let rec make_term tt =
  (*Format.eprintf "Make_term: %a@." Types.Term.print tt; *)
  match tt with 
    | Elem (e, _) ->
      (*Format.eprintf "Elemt is %a@." Hstring.print e;*) 
      let tyl, ty = Smt.Symbol.type_of e in
      (*Format.printf "ty: %a@." Hstring.print ty;*)
      List.iter (Format.eprintf "tyl: %a@." Hstring.print) tyl;
      T.make_app e []
  | Const cs -> make_cs cs 
  | Access (a, li)  ->
    T.make_app a (List.map (fun i -> T.make_app i []) li)
  | Arith (x, cs) -> 
      let tx = make_term x in
      make_arith_cs cs tx
  | UnOp (o,t1) -> Format.eprintf "ici@."; assert false
  | BinOp (t1, op, t2) -> Format.eprintf "ici@."; assert false
  | Record lbs ->
    let record = Smt.Type.record_ty_by_field (fst (List.hd lbs)) in
    let ls = List.map (fun (f,t) -> make_term t) lbs in

    T.make_record record ls 
      
  | RecordWith (t, htl)  ->    
    let lh = fst (List.hd htl) in
    let (_, fields) as record = Smt.Type.record_ty_by_field lh in
    let comp = List.filter (fun (lbl,_) -> not (List.exists (fun (x,_) -> Hstring.compare lbl x = 0) htl )) fields in
    
    let n_comp = List.map (fun (lbl,_) -> lbl,make_term (RecordField(t, lbl))) comp in

    let htl =
      List.fold_left (fun ls (lbl, v) -> (lbl, make_term v)::ls) n_comp htl in
    
    let n_fields = List.sort Smt.Type.compare_rec htl in
    let n_fields = List.map snd n_fields in 

    T.make_record record n_fields 
    
  | RecordField (record, field) ->
    let t_record = make_term record in
    let nre, re = Smt.Type.record_ty_by_field field  in
    let ty_field= Hstring.list_assoc field re in
    T.make_field field t_record ty_field
      
  | Null (_,t) ->
    let n, l = Smt.Type.record_type_details t in
	  T.make_record (n,l) []
    (*begin
      match te with
	| None  
	| Some _ -> Format.eprintf "t is %a@." Hstring.print t;
	  let _n, _l = Smt.Type.record_type_details t in
	  T.make_record (_n,_l) []
    end*)

    
let extract_with l lbs =
  let tab = Term.HMap.create 17 in  
  List.iter (fun t ->
      match t with
	| RecordField(r,_) ->
	  begin
	    try
	      Term.HMap.replace tab r (Term.HMap.find tab r+1)
	    with Not_found -> Term.HMap.add tab r 1
	  end
	| _ -> ()) l;
  let max =
    let max =
      Term.HMap.fold (fun k n xopt ->
	match xopt with
	  | Some (_,xn) -> if n > xn then Some(k,n) else xopt
	  | None -> if n > 1 then Some (k,n) else xopt
      ) tab None
    in
    match max with Some (x,_) -> Some x | _ -> None
  in 
  let eq_max lbl = 
    match max with
      | None -> false
      | Some x -> Types.Term.compare x lbl = 0
  in
  max, List.fold_right2 (fun (a,_) t acc ->
    match t with
      | RecordField(r,_) ->
	if eq_max r then acc else (a,t)::acc
      | _ -> (a,t)::acc 

  ) lbs l []
      
let rec convert_term t =
  if debug_normalize then 
  Format.eprintf "[normalize: convert term] Convert term t: %a @." T.print t;
    (*type view = private {f: Symbols.t ; xs: t list; ty: Ty.t; tag : int}
    *)
    let tt = T.view_symbol t in 
    match tt  with  
      | True -> Elem (Hstring.make "@MTrue", Constr)
      | False -> Elem (Hstring.make "@MFalse", Constr)
      | Name (h, nk) ->
	begin
	  match nk with
	    | Constructor -> Elem (h, Constr)
	    | Other ->
	      let xs = T.view_xs t in
	      if xs = [] then 
		Elem (h,Glob)
	      else 
		let l = List.map (fun x ->
		  match T.view_symbol x with
		    | Name (n', _) -> n'
		    | _ -> assert false) xs in
		Access(h, l)
	    | Ac -> assert false
	end 
      | Int i -> Const(MConst.add (ConstInt (Num.num_of_string (Hstring.view i))) 1 MConst.empty)
      | Real r -> Const(MConst.add (ConstReal (Num.num_of_string (Hstring.view r))) 1 MConst.empty)
      | Op o ->
	begin
	  let xs = List.map convert_term (T.view_xs t) in
	  match o, xs with
	    | Plus, [el] -> el
	    | Plus, _
	    | Minus, _
	    | Mult, _
	    | Div , _
	    | Modulo , _ -> assert false	     
	    | Record, l ->
		begin
		  match T.view_ty t with
		    | Trecord { name = name; lbs = lbs } ->
		      if T.view_xs t = [] then Null (None, name)
		      else
		      begin
		      match extract_with l lbs with
			| None, wl -> Record wl
			  
			| Some w, wl -> RecordWith(w, wl)
		      end
		    | _ -> assert false 
	
		end 
	    | Access h, [el] -> RecordField(el, h)
	    | Access h, _ -> assert false
	end
	  
      | Var v -> assert (T.view_ty t = Tint); Elem (v, Var)
      | _ -> assert false
     
      

let rec make_formula_set sa = 
 F.make F.And (SAtom.fold (fun a l ->  make_literal a::l) sa []) 


and make_literal = function
  | Atom.True ->  F.f_true 
  | Atom.False -> F.f_false
  | Atom.Comp (x, op, y) ->
    let tx = make_term x in
    let ty = make_term y in
    F.make_lit (make_op_comp op) [tx; ty]
  | Atom.Ite (la, a1, a2) ->
      let f = make_formula_set la in
      let a1 = make_literal a1 in
      let a2 = make_literal a2 in
      let ff1 = F.make F.Imp [f; a1] in
      let ff2 = F.make F.Imp [F.make F.Not [f]; a2] in
      F.make F.And [ff1; ff2]


let make_formula atoms =
  F.make F.And (Array.fold_left (fun l a -> make_literal a::l) [] atoms)

module HAA = Hashtbl.Make (ArrayAtom)

let make_formula =
  let cache = HAA.create 200001 in
  fun atoms ->
    try HAA.find cache atoms
    with Not_found ->
      let f = make_formula atoms in
      HAA.add cache atoms f;
      f

let make_formula array =
  TimeFormula.start ();
  let f = make_formula array in
  TimeFormula.pause ();
  f

let make_formula_set satom =
  TimeFormula.start ();
  let f = make_formula_set satom in
  TimeFormula.pause ();
  f


let make_disjunction nodes = F.make F.Or (List.map make_formula nodes)


let make_conjuct atoms1 atoms2 =
  let l = Array.fold_left (fun l a -> make_literal a::l) [] atoms1 in
  let l = Array.fold_left (fun l a -> make_literal a::l) l atoms2 in
  F.make F.And l


let make_init_dnfs s nb_procs =
  let { init_cdnf } = Hashtbl.find s.t_init_instances nb_procs in
   List.rev_map (List.rev_map make_formula_set) init_cdnf 

let get_user_invs s nb_procs =
  let { init_invs } =  Hashtbl.find s.t_init_instances nb_procs in
  List.rev_map (fun a -> F.make F.Not [make_formula a]) init_invs

let unsafe_conj { tag = id; cube = cube } nb_procs invs init =
  if debug_smt then eprintf ">>> [smt] safety with: %a@." F.print init;
  SMT.clear ();

      SMT.assume ~id (distinct_vars nb_procs);

  List.iter (SMT.assume ~id) invs;

  (*Format.eprintf "litterals: %a@." Types.SAtom.print cube.Cube.litterals;*)
  let f = make_formula_set cube.Cube.litterals in
  if debug_smt then eprintf "[smt] safety: %a and %a@." F.print f F.print init;
  (*Format.eprintf "Assume1@.";*)
  SMT.assume ~id init;
  (*Format.eprintf "Assume1 done@.";*)
  (*Format.eprintf "F pre assume 2: %a@." F.print f ;*)
  (*Format.eprintf "Assume 2 @.";*)
  SMT.assume ~id f;
  (*Format.eprintf "Assume2 done@.";*)
  SMT.check ()
  (*Format.eprintf "Check done@."*)

let unsafe_dnf node nb_procs invs dnf =
  try
    let uc =
      List.fold_left (fun accuc init ->
        try
          unsafe_conj node nb_procs invs init;
          raise Exit
        with Smt.Unsat uc -> List.rev_append uc accuc) [] dnf
    in
    raise (Smt.Unsat uc)
  with Exit -> ()

let unsafe_cdnf s n =
  let nb_procs = List.length (Node.variables n) in
  let cdnf_init = make_init_dnfs s nb_procs in
  let invs = get_user_invs s nb_procs in
  List.iter (unsafe_dnf n nb_procs invs) cdnf_init

let unsafe s n = unsafe_cdnf s n


let reached args s sa =
  SMT.clear ();

  SMT.assume ~id:0 (distinct_vars (List.length args));
  let f = make_formula_set (SAtom.union sa s) in

  SMT.assume ~id:0 f;
  SMT.check ()


let assume_goal_no_check { tag = id; cube = cube } =
  SMT.clear ();
  (*Format.eprintf "Fuck1 %d@." (List.length cube.Cube.vars);
  let hhh = distinct_vars (List.length cube.Cube.vars) in
  Format.eprintf ": %a@." F.print hhh;*)
  SMT.assume ~id (distinct_vars (List.length cube.Cube.vars));
  let f = make_formula cube.Cube.array in
  (*Format.eprintf "goals--: %a@." Types.ArrayAtom.print cube.Cube.array;*)
  
  if debug_smt then eprintf "[smt] goal g: %a@." F.print f;

  SMT.assume ~id f

let assume_node_no_check { tag = id } ap =
  let f = F.make F.Not [make_formula ap] in
  if debug_smt then eprintf "[smt] assume node: %a@." F.print f;
  SMT.assume ~id f

let assume_goal n =
  assume_goal_no_check n;
  SMT.check  ()

let assume_node n ap =
  assume_node_no_check n ap;
  SMT.check  ()


let run () = SMT.check ()

let check_guard args sa reqs =
  SMT.clear ();
  SMT.assume ~id:0 (distinct_vars (List.length args));
  let f = make_formula_set (SAtom.union sa reqs) in
  SMT.assume ~id:0 f;
  SMT.check ()

let assume_goal_nodes { tag = id; cube = cube } nodes =
  SMT.clear ();

  SMT.assume ~id (distinct_vars (List.length cube.Cube.vars));
  let f = make_formula cube.Cube.array in
  if debug_smt then eprintf "[smt] goal g: %a@." F.print f;
  SMT.assume ~id f;
  List.iter (fun (n, a) -> assume_node_no_check n a) nodes;
  SMT.check  ()


    
let canonize a =
    match a with
      | Atom.Comp (t1, op, t2) ->
	if debug_normalize then
	  begin
	Format.eprintf "[normalize: canonize] @.";
	    Format.eprintf "Term1 op Term2 : %a %s %a  @." Types.Term.print t1 (Types.Atom.str_op_comp op) Types.Term.print t2
	  end;

	let nt1 = make_term t1 in
	let nt2 = make_term t2 in
	let nt1 = match Combine.CX.term_extract ( fst (Combine.CX.make nt1)) with
	  | Some nt1 -> nt1
	  | None -> nt1
	in
	let nt2 = match Combine.CX.term_extract ( fst (Combine.CX.make nt2 ))with
	  | Some nt2 ->  nt2
	  | None -> nt2
	in
	if debug_normalize then 
	Format.eprintf "[normalize: canonize2] pre nt1 converted: %a and pre nt2 converted %a@." T.print nt1 T.print nt2;
	let nt11 = convert_term nt1 in
	let nt21 = convert_term nt2 in
	if debug_normalize then 
	Format.eprintf "[normalize: canonize3] nt1 converted: %a and nt2 converted %a@." Types.Term.print nt11 Types.Term.print nt21;
	Atom.Comp (convert_term nt1, op,  convert_term nt2)
      | _ -> a
  

let check_terms (h1,t1) (h2,t2) =
  if Str.string_match (Str.regexp "!k[0-9]*$") (Hstring.view h1) 0 ||  Str.string_match (Str.regexp "!k[0-9]*$") (Hstring.view h2) 0 then None
  else Some (Atom.Comp (t1, Eq, t2))
  
	
let filter_map2 l1 l2 =
  let l =
    let rec aux acc l1 l2 = 
      match l1, l2 with
	| [], [] -> List.rev acc 
	| hd1::tl1, hd2::tl2 ->
	  begin 
	    match check_terms hd1 hd2 with
	      | None -> aux acc tl1 tl2
	    | Some s -> aux (s::acc) tl1 tl2
	  end
	| _, _ -> assert false
    in aux [] l1 l2
  in
  List.fold_right (fun el acc -> SAtom.add el acc) l SAtom.empty  
	 
let extract_term op (*sa*) acc lit =
  let nt1, nt2 = F.lit_to_terms lit in
  let cn1 = convert_term nt1 in
  let cn2 = convert_term nt2 in
  if debug_normalize then 
  Format.eprintf "[normalize: extract-term] Term1 op Term2: %a %s %a@." Types.Term.print cn1 (Types.Atom.str_op_comp op) Types.Term.print cn2;
  match cn1, cn2 with
	    | Elem (h,_), Elem (h1, _) ->
	      if Str.string_match (Str.regexp "!k[0-9]*$") (Hstring.view h) 0 ||  Str.string_match (Str.regexp "!k[0-9]*$") (Hstring.view h1) 0 then acc
	      else SAtom.add (Atom.Comp (cn1, op, cn2)) acc
	    | Elem (h, _), _ | _, Elem (h, _) when Str.string_match (Str.regexp "!k[0-9]*$") (Hstring.view h) 0 ->
	      acc
	    | Record l1, Record l2 ->
	      let sal = filter_map2 l1 l2 in
	      if SAtom.is_empty sal then SAtom.add (Atom.Comp (cn1, op, cn2)) acc
	      else SAtom.union sal acc
	    | Record l, _  | _, Record l -> 
	      let filter2 l1 =
		let rec aux acc1 l2 b =
		  match l2 with
		    | [] -> if b then Some acc1 else None
		    | (h,t)::tl ->
		      begin
			match t with
			  | Elem (h1,_) ->
			    if Str.string_match (Str.regexp "!k[0-9]*$") (Hstring.view h1) 0 then aux acc1 tl true 
				else aux (Atom.Comp (RecordField(cn1, h), Eq, t)::acc1) tl b
			  | _ -> aux (Atom.Comp (RecordField(cn1, h), Eq, t)::acc1) tl b
		      end
		in aux [] l1 false
	      in 		  
	      begin
		match filter2 l with
		  | None -> SAtom.add (Atom.Comp (cn1, op, cn2)) acc
		  | Some s -> List.fold_right (fun el acc -> SAtom.add el acc) s SAtom.empty
	      end
	    | _, _ -> SAtom.add (Atom.Comp (cn1, op, cn2)) acc
  
	
let normalize s =
  let sf = SAtom.fold ( fun a cn ->
    match a with
      | Comp (Null _, op, _) 
      | Comp (_, op, Null _) -> SAtom.add a cn
      | Comp (t1, ((Eq ) as op) , t2) ->
	let r1 = make_term t1 in
	let r2 = make_term t2 in
	let op1 = (match op with Eq -> F.Eq | Neq -> Neq | _ -> assert false) in 
	let lit = F.terms_to_lit op1 [r1;r2] in
	let nlit = SMT.normalize lit (*op1*) in
	let nt =
	  List.fold_left (extract_term op) SAtom.empty nlit 
	in
	SAtom.union cn nt
      | _ -> SAtom.add (canonize a) cn
  ) s SAtom.empty
  in
  if debug_normalize then
    begin
      Format.eprintf "[normalize: normalize]@.";
      Format.eprintf "Pre-normalized s: %a@." Types.SAtom.print s;
      Format.eprintf "Post-normalized s: %a@." Types.SAtom.print sf;
    end
  else ();
  sf


let normalize s = s
