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

type error = 
  | DuplicateTypeName of Hstring.t
  | DuplicateSymb of Hstring.t
  | DuplicateLabel of Hstring.t
  | UnknownType of Hstring.t
  | UnknownSymb of Hstring.t
  | UnknownLabel of Hstring.t 

exception Error of error

let report fmt = function
  | DuplicateTypeName s ->
    fprintf fmt "duplicate type name for %a" Hstring.print s
  | DuplicateSymb e ->
    fprintf fmt "duplicate name for %a" Hstring.print e
  | DuplicateLabel s ->
    fprintf fmt "duplicate name for %a" Hstring.print s
  | UnknownType s ->
    fprintf fmt "unknown type %a" Hstring.print s
  | UnknownSymb s ->
    fprintf fmt "unknown symbol %a" Hstring.print s
  | UnknownLabel s ->
    fprintf fmt "unknown label %a" Hstring.print s 


type check_strategy = Lazy | Eager
                      
module H = Hstring.H
module HSet = Hstring.HSet

let decl_types = H.create 17
let decl_symbs = H.create 17
let decl_labels = H.create 17

let htrue = Hstring.make "True"
let hfalse = Hstring.make "False"


module Type = struct

  type t = Hstring.t

  let equal = Hstring.equal


  let type_int = 
    let tint = Hstring.make "int" in
    H.add decl_types tint Ty.Tint;
    tint

  let type_real = 
    let treal = Hstring.make "real" in
    H.add decl_types treal Ty.Treal;
    treal

  let type_bool = 
    let tbool = Hstring.make "bool" in
    H.add decl_types tbool Ty.Tbool;
    tbool

  let type_proc = 
    let tproc = Hstring.make "proc" in
    H.add decl_types tproc Ty.Tint;
    tproc


      

  let declare_constructor ty c = 
    if H.mem decl_symbs c then raise (Error (DuplicateSymb c));
    H.add decl_symbs c 
      (Symbols.name ~kind:Symbols.Constructor c, [], ty)

  let declare_enum t constrs = 
    if H.mem decl_types t then raise (Error (DuplicateTypeName t));
    match constrs with
      | [] -> 
	  H.add decl_types t (Ty.Tabstract t)
      | _ -> 
	  let ty = Ty.Tsum (t, constrs) in
	  H.add decl_types t ty;
	  List.iter (fun c -> declare_constructor t c) constrs

  let all_constructors () =
    H.fold (fun _ c acc -> match c with
      | Symbols.Name (h, Symbols.Constructor), _, _ -> h :: acc
      | _ -> acc
    ) decl_symbs [htrue; hfalse]

  let constructors ty =
    if Hstring.equal ty type_bool then [htrue; hfalse]
    else match H.find decl_types ty with
      | Ty.Tsum (_ , cstrs) -> cstrs
      | _ -> []

  let compare_rec (x,y) (x',y') =
    Hstring.compare x x'

 

  let declare_record ty l =
    if H.mem decl_types ty then raise (Error (DuplicateTypeName ty));
    let new_list = List.fold_left (fun acc (f_n, f_ty) ->
      if not (H.mem decl_types f_ty) then raise (Error (UnknownType f_ty));
      if H.mem decl_labels f_n then raise (Error (DuplicateLabel f_n))
      else
	begin
	  H.add decl_labels f_n (ty, f_ty, l);
	  (*H.add decl_symbs f_n (Symbols.name f_n, [], f_ty)*)
	end;
	
      let fty_ty =
	try H.find decl_types f_ty
	with Not_found -> raise (Error(UnknownType f_ty))
      in (f_n, fty_ty)::acc
      
    ) [] l in
    let l1 = List.sort compare_rec new_list in
    H.add decl_types ty (Ty.Trecord {name = ty; lbs = l1})
 

  let all_record_types () =
    let d = H.to_seq_values decl_types in
    Seq.fold_left (fun acc v ->
      match v with
	| Ty.Trecord {name = re; lbs = l} -> (re,l)::acc
	| _ -> acc
    ) [] d

  let record_field_type lbl =
    try let _, fty, _ = H.find decl_labels lbl
	in fty
    with Not_found -> raise (Error (UnknownLabel lbl))

  let record_field_ty lbl =
    assert false

  let record_ty_by_field lbl =
    let rty, _, fields= H.find decl_labels lbl
    in
	try let r = H.find decl_types rty in
	    match r with
	      | Ty.Trecord {name = re; lbs = l} ->
				re,l
	      | _ -> raise (Error (UnknownType rty))
	  with Not_found -> raise (Error (UnknownType rty))

  let find_record_by_field lbl =
    let rty, _, fields= H.find decl_labels lbl
	in
    rty, fields

  let is_record ty  =
    match H.find decl_types ty with
      | Ty.Trecord _ -> true
      | _ -> false

  let is_record_opt ty =
    match H.find decl_types ty with
      | Ty.Trecord {lbs = lbs } -> let l = List.map fst lbs in Some l
      | _ -> None
	   
	
  let record_type_details t =
    match H.find decl_types t with
      | Ty.Trecord { name = name; lbs = lbs } -> name, lbs
      | _ -> assert false
    
      
      
  let declared_types () =
    H.fold (fun ty _ acc -> ty :: acc) decl_types []

  let record_type_details t =
    match H.find decl_types t with
      | Ty.Trecord { name = name; lbs = lbs } -> name, lbs
      | _ -> assert false
       
	


end

module Symbol = struct
    
  type t = Hstring.t

  let declare f args ret  =
    if H.mem decl_symbs f then raise (Error (DuplicateTypeName f));
    List.iter 
      (fun t -> 
	if not (H.mem decl_types t) then raise (Error (UnknownType t)) )
      (ret::args);
    H.add decl_symbs f (Symbols.name f, args, ret);
    match Type.is_record_opt ret with
      | None -> ()
      | Some l ->
	let f' = Hstring.view f in 
	List.iter (fun fd ->
	  let fd' = Hstring.view fd in
	  let nfd = Hstring.make (f'^fd') in
	  let _,fty,_ = H.find decl_labels fd in
	  H.add decl_symbs nfd (Symbols.name nfd, [], fty)
	) l
  
   

  let type_of s = let _, args, ret =  H.find decl_symbs s in  args, ret
    
    

  let declared s =
    let res = H.mem decl_symbs s in
    if not res then begin 
      eprintf "Not declared : %a in@." Hstring.print s;
      H.iter (fun hs (sy, _, _) ->
	eprintf "%a (=?%b) -> %a@." Hstring.print hs 
	  (Hstring.compare hs s = 0)
	  Symbols.print sy)
	  decl_symbs;
      end;
      res

  let not_builtin ty = Hstring.equal ty Type.type_proc ||
    not (Hstring.equal ty Type.type_int || Hstring.equal ty Type.type_real ||
	   Hstring.equal ty Type.type_bool || Hstring.equal ty Type.type_proc)
    
  let has_abstract_type s =
    let _, ret = type_of s in
    match H.find decl_types ret with
      | Ty.Tabstract _ -> true
      | _ -> false

  let has_infinite_type s =
    let _, ret = type_of s in
    Hstring.equal ret Type.type_real ||
    Hstring.equal ret Type.type_int ||
    (* Hstring.equal ret Type.type_proc || *)
    match H.find decl_types ret with
      | Ty.Tabstract _ -> true
      | _ -> false
     
  let has_type_proc s =
    Hstring.equal (snd (type_of s)) Type.type_proc
      
  let _ = 
    H.add decl_symbs htrue (Symbols.True, [], Type.type_bool);
    H.add decl_symbs hfalse (Symbols.False, [], Type.type_bool);
    
end

module Variant = struct
    
  let constructors = H.create 17
  let assignments = H.create 17

  module R = Set.Make (struct
    type t = Hstring.t * Hstring.t
    let compare (a,b) (x,y) =
      let c = Hstring.compare a x in
      if c = 0 then Hstring.compare b y
      else c
  end)

  let record_assignments = H.create 17
  let rec_constructors = H.create 17


  let find t x = try H.find t x with Not_found -> HSet.empty

  let find_record t x = try H.find t x with Not_found -> R.empty

    
  let get_variants = H.find constructors
    
  let set_of_list = List.fold_left (fun s x -> HSet.add x s) HSet.empty 
    
    
  let add t x v = 
    let s = find t x in
    H.replace t x (HSet.add v s)

  let add_record_constr g (field, el)  =
    if Options.debug_subtypes then
      begin
	Format.eprintf "[debug subtypes] add record constructor:@.";
	Format.eprintf "g: %a, field: %a; el: %a@."
	  Hstring.print g Hstring.print field Hstring.print el;
      end;
    let curr = (*(Hstring.t * HSet.t option) list *)
      try H.find rec_constructors g
      with Not_found -> []	
    in
    let flag, l =
      if curr = [] then
	begin
	  let s = HSet.add el HSet.empty in true, [(field,Some s)]
	end
      else
	begin
	  List.fold_left (fun (flag,acc) (f, so) ->
	    if Options.debug_subtypes then
	      Format.eprintf "[debug sybtypes] f in fold_left: %a@." Hstring.print f;
	      begin
		match so with
		  | None -> flag,((f,so)::acc)
	      (* assert false since called from typing, so it shouldn't not be a constructor*)
		  | Some s ->
		    if Hstring.equal field f then	      
		      let s = HSet.add el s in
		      true, ((f, Some s)::acc)
		    else
		      flag,((f, so)::acc)	      
	      end 
	    
	  ) (false,[]) curr
	end
    in
    let l =
      if not flag then
	let s = HSet.add el HSet.empty in (field, Some s)::l
      else l
    in 
    H.replace rec_constructors g l 
      
  let assign_constr = add constructors

  let hset_print fmt s = 
    HSet.iter (fun c -> Format.eprintf "%a, " Hstring.print c) s
    
  let assign_var x y = 
    if not (Hstring.equal x y) then
      add assignments x y

  let assign_record g fconstr =
    let s =
      try H.find record_assignments g with
	  Not_found -> R.empty
    in
    H.replace record_assignments g (R.add fconstr s) 
    	  
  let rec compute () =
    let flag = ref false in
    let visited = ref HSet.empty in
    let rec dfs x s =
      if not (HSet.mem x !visited) then
	begin
	  visited := HSet.add x !visited;
	  HSet.iter 
	    (fun y -> 
	      let c_x = find constructors x in
	      let c_y = find constructors y in
	      let c = HSet.union c_x c_y in
	      if not (HSet.equal c c_x) then
		begin
		     H.replace constructors x c;
		     flag := true
		end;
	      dfs y (find assignments y)
	    ) s
	end
    in
    H.iter dfs assignments;
    if !flag then compute ()


  let rec compute_records () =
    let flag = ref false in
    let visited = ref HSet.empty in
    let rec search g set_of_values =
      if not (HSet.mem g !visited) then  
	begin
	  visited := HSet.add g !visited;
	  R.iter (
	    fun (field, elem) -> 
	      let c_g =
		try H.find rec_constructors g
		with Not_found -> assert false (* the record should exist *)
	      in
	      let c_elem = find constructors elem
	      in
	      let l =
		List.map (fun (fd, so) ->
		  if Hstring.equal fd field then
		    begin
		      match so with
			| None -> assert false (* shouldn't happen *)
			| Some s ->
			  let s' = HSet.union s c_elem
			  in
			  if not (HSet.equal s s') then flag := true;
			  (fd, Some s')
		    end
		  else (fd, so)
		) c_g
	      in
	      H.replace rec_constructors g l 
	  ) set_of_values
	    (* [ (field, option set of constr) ]
		if a field is type constr, then it has a Some set 
	       of the poss values of the constr. 
	       If the field is not a constr then None
	    *)
	end
    in
    H.iter search record_assignments;
    if !flag then compute_records ()
    
    
  let print () =
    H.iter 
      (fun x c -> 
         Format.eprintf "%a : %a = {%a}@."
           Hstring.print x
           Hstring.print (snd (Symbol.type_of x))
           hset_print c) 
      constructors


  let init l =
    compute ();
    compute_records ();

    List.iter 
      (fun (x, nty) ->
	  let ty = H.find decl_types nty in
	  match ty with
	    | Ty.Tsum (_, l) ->
	      	if not (H.mem constructors x) then
		  H.add constructors x (set_of_list l)
	    | Ty.Trecord {name = name; lbs = lbs} ->
	      
	      begin
	      try
		let curr = H.find rec_constructors x in
		let mm =
		  List.fold_left  (fun acc (field, typ) ->
		    match typ with
		      | Ty.Tsum (_, ls) ->
			let l'= 
			  try
			    Hstring.list_assoc field curr
			  with Not_found -> Some (set_of_list ls) 
			in
			(field, l')::acc
		      | _ -> acc
			
		   
		  ) [] lbs
		in
		H.replace rec_constructors x mm
	      with
		  Not_found ->
		    begin
		      let ll =
			List.map (fun (field, typ) ->
			  match typ with
			    | Ty.Tsum (_, ls) -> 
				  field, Some (set_of_list ls)
			    | _ -> field, None
			) lbs
		      in
			  H.add rec_constructors x ll
		    end
	      end
		  
	    | _ -> ()) l;
    H.clear assignments;
    H.clear record_assignments

  let update_decl_types s old_ty x =
    let new_ty = Hstring.(view old_ty ^ "_" ^ view x |> make) in
    let l = HSet.elements s in
    let ty = Ty.Tsum (new_ty, (* List.rev *) l) in
    H.replace decl_types new_ty ty;
    new_ty

  let close () = 
    compute ();
    compute_records ();
    H.iter 
      (fun x s ->
	let sy, args, old_ty = H.find decl_symbs x in
	let nty = update_decl_types s old_ty x in
	H.replace decl_symbs x (sy, args, nty))
      constructors;

    
    H.iter (fun g l ->
      match l with
	| [] -> ()
	| _ -> 
	  let sy, args, old_ty = H.find decl_symbs g in
	  let ll = 
	    List.map (fun (field, so) ->
	      match so with
		| None -> (field, None, None)
		| Some s ->
		  let s' = HSet.elements s in
		  let ty_new = Hstring.(view old_ty ^ "_"^view g ^"_" ^view field)  in
		  let ty_new = Hstring.make ty_new in
		  let ty = Ty.Tsum (ty_new, s') in
		  H.replace decl_types ty_new ty;
		  (field, Some ty, Some ty_new)
	    ) l	      
	  in      
	  let tr =
	    try
	      H.find decl_types old_ty
	    with Not_found -> assert false
	  in
	  begin
	    match tr with
	      | Ty.Trecord {name = name; lbs = lbs } ->
		let l' =
		  (*
		  List.map2 (fun (f1, t1, no1) (f2, t2) ->
		    if not (Hstring.equal f1 f2) then assert false;
		    match t1 with
		      | None -> f2, t2
		      | Some s -> f2, s
		    ) ll lbs*) 
		  List.map (fun (f2, t2) ->
		    let el' =
		      List.fold_left (fun acc (f1, t1, no1) ->
			if Hstring.equal f1 f2 then
			  begin
			    match t1 with
			      | None -> acc
			      | Some s -> Some (f2, s)
			  end
			else
			  acc) None ll
		    in
		    match el' with
		      | None -> f2, t2
		      | Some s -> s
		  ) lbs
		    
		in
		let nname = Hstring.(view old_ty ^ "_" ^view g) in
		let nname = Hstring.make nname in 
		let ntr = Ty.Trecord { name = nname; lbs = l' }
		in
		(*List.iter (fun (f,t) -> Format.eprintf "ugh: %a : %a@." Hstring.print f Ty.print t) l';*)
		H.replace decl_types nname ntr;
		H.replace decl_symbs g (sy, args, nname);

		(*List.iter2 (fun (f1, t1, no1) (f2, t2) ->
		  if not (Hstring.equal f1 f2) then assert false;
		  match t1,no1 with
		    | None, None -> ()
		    | Some st, Some sno ->
		      let _,_,ugh = H.find decl_labels f1 in
		      H.replace decl_labels f1 (nname, sno, ugh)
		    | _ -> assert false
		  ) ll lbs*)

		List.iter (fun (f2, t2) ->
		  List.iter (fun (f1, t1, no1) ->
		    if Hstring.equal f1 f2 then
		      begin
		    match t1, no1 with
		      | None, None -> ()
		      | Some st, Some sno ->
			let _,_,ugh = H.find decl_labels f1 in
			H.replace decl_labels f1 (nname, sno, ugh)
		      | _ -> assert false
		      end
		    else ()
		      ) ll
		) lbs
		  
	      | _ -> (*Format.eprintf "g was: %a@." Hstring.print g;*) assert false
	  end

	   (* let _,_,ttt = H.find decl_symbs g in
	    Format.eprintf "g is now: %a : %a@." Hstring.print g Hstring.print ttt*)


    ) rec_constructors;

    
    if Options.debug_subtypes then
      begin 
    Format.eprintf "---------------Debug Subtyping---------------@.";
    Format.eprintf "All types:@."; 
    let ttt = Type.declared_types () in
    List.iter (fun x ->
      let tx = H.find decl_types x in
      Format.eprintf "type %a : %a@." Hstring.print x Ty.print tx
    ) ttt;
    Format.eprintf "---------------------------------------------@.";
      end 
      
    
      
end

  
module Term = struct

  type t = Term.t
  type operator = Plus | Minus | Mult | Div | Modulo 

  let make_int i = Term.int (Num.string_of_num i)

  let make_real r = Term.real (Num.string_of_num r)

  let make_app s l =
    try
      let (sb, _, nty) = H.find decl_symbs s in
      let ty = H.find decl_types nty in
      Term.make sb l ty
    with Not_found -> raise (Error (UnknownSymb s))

  let t_true = Term.vrai
  let t_false = Term.faux

  let make_arith op t1 t2 = 
    let op = 
      match op with
	| Plus -> Symbols.Plus
	| Minus -> Symbols.Minus
	| Mult ->  Symbols.Mult
	| Div -> Symbols.Div
	| Modulo -> Symbols.Modulo
    in
    let ty = 
      if Term.is_int t1 && Term.is_int t2 then Ty.Tint
      else if Term.is_real t1 && Term.is_real t2 then Ty.Treal
      else assert false
    in
    Term.make (Symbols.Op op) [t1; t2] ty

  let make_record (rec_name, rec_fields) terms  =
    Term.make (Symbols.Op Symbols.Record) terms (Ty.Trecord {name = rec_name; lbs = rec_fields})

  let make_field field term ty_field=
    Term.make (Symbols.Op (Symbols.Access (field))) [term] ty_field
    
  let is_int = Term.is_int

  let is_real = Term.is_real

  let print = Term.print

  let compare = Term.compare

  let view_symbol t = (Term.view t).f

  let view_ty t = (Term.view t).ty

  let view_xs t = (Term.view t).xs
  let is_proc p = let _, args, _ = H.find decl_symbs p in args
    

end

module Formula = struct

  type comparator = Eq | Neq | Le | Lt
  type combinator = And | Or | Imp | Not

  type literal = Literal.LT.t
  
  type t = 
    | Lit of literal
    | Comb of combinator * t list

  let rec print fmt phi = 
    match phi with
      | Lit a -> Literal.LT.print fmt a
      | Comb (Not, [f]) -> 
	  fprintf fmt "not (%a)" print f
      | Comb (And, l) -> fprintf fmt "(%a)" (print_list "and") l
      | Comb (Or, l) ->  fprintf fmt "(%a)" (print_list "or") l
      | Comb (Imp, [f1; f2]) -> 
	  fprintf fmt "%a => %a" print f1 print f2
      | _ -> assert false
  and print_list sep fmt = function
    | [] -> ()
    | [f] -> print fmt f
    | f::l -> fprintf fmt "%a %s %a" print f sep (print_list sep) l

  let f_true = Lit Literal.LT.vrai
  let f_false = Lit Literal.LT.faux

  let make_lit cmp l =
    let lit = 
      match cmp, l with
	| Eq, [t1; t2] -> 
	   Literal.Eq (t1, t2) 
	| Neq, ts -> 
	    Literal.Distinct (false, ts)
	| Le, [t1; t2] ->
	    Literal.Builtin (true, Hstring.make "<=", [t1; t2])
	| Lt, [t1; t2] ->
	    Literal.Builtin (true, Hstring.make "<", [t1; t2])
	| _ -> assert false
    in
    Lit (Literal.LT.make lit)

  let terms_to_lit cmp l =
    let lit =
      match cmp, l with
	| Eq, [t1;t2] -> Literal.Eq (t1,t2)
	| Neq, t -> Literal.Distinct (false, t)
	| _ -> assert false
    in [Literal.LT.make lit]

  let lit_to_terms lit =
    match Literal.LT.view lit with
      | Eq (t1, t2) 
      | Distinct (_, [t1;t2]) 
      | Builtin (_, _, [t1;t2]) -> t1,t2
      | _ -> assert false

  let rec sform = function
    | Comb (Not, [Lit a]) -> Lit (Literal.LT.neg a)
    | Comb (Not, [Comb (Not, [f])]) -> f
    | Comb (Not, [Comb (Or, l)]) ->
	let nl = List.map (fun a -> sform (Comb (Not, [a]))) l in
	Comb (And, nl)
    | Comb (Not, [Comb (And, l)]) ->  
	let nl = List.map (fun a -> sform (Comb (Not, [a]))) l in
	Comb (Or, nl)
    | Comb (Not, [Comb (Imp, [f1; f2])]) -> 
	Comb (And, [sform f1; sform (Comb (Not, [f2]))])
    | Comb (And, l) -> 
	Comb (And, List.map sform l)
    | Comb (Or, l) -> 
	Comb (Or, List.map sform l)
    | Comb (Imp, [f1; f2]) -> 
	Comb (Or, [sform (Comb (Not, [f1])); sform f2])
    | Comb (Imp, _) -> assert false
    | f -> f

  let make comb l = Comb (comb, l)

  let make_or = function
    | [] -> assert false
    | [a] -> a
    | l -> Comb (Or, l)

  let distrib l_and l_or = 
    let l = 
      if l_or = [] then l_and
      else
	List.map 
	  (fun x -> 
	     match x with 
	       | Lit _ -> Comb (Or, x::l_or)
	       | Comb (Or, l) -> Comb (Or, l@l_or)
	       | _ -> assert false
	  ) l_and 
    in
    Comb (And, l)

  let rec flatten_or = function
    | [] -> []
    | Comb (Or, l)::r -> l@(flatten_or r)
    | Lit a :: r -> (Lit a)::(flatten_or r)
    | _ -> assert false
    
  let rec flatten_and = function
    | [] -> []
    | Comb (And, l)::r -> l@(flatten_and r)
    | a :: r -> a::(flatten_and r)
    
  let rec cnf f = 
    match f with
      | Comb (Or, hd::tl) ->
	begin
	  let hd' = cnf hd in
	  let tl' = cnf (Comb (Or, tl)) in
	  match hd', tl' with
	    | hd', Comb (And, tl') ->
	      Comb (And, List.map (fun x -> cnf (Comb (Or, [hd'; x]))) tl')
	    | Comb (And, hd'), tl' ->
	      Comb (And, List.map (fun x -> cnf (Comb (Or, [x; tl']))) hd')
	    | _, _ -> f 
	end
      | Comb (And, l) -> 
	  Comb (And, List.map cnf l)
      | f -> f


let ( @@ ) l1 l2 = List.rev_append l1 l2

let rec mk_cnf = function
  | Comb (And, l) ->
      List.fold_left (fun acc f ->  (mk_cnf f) @@ acc) [] l

  | Comb (Or, [f1;f2]) ->
      let ll1 = mk_cnf f1 in
      let ll2 = mk_cnf f2 in
      List.fold_left 
	(fun acc l1 -> (List.rev_map (fun l2 -> l1 @@ l2)ll2) @@ acc) [] ll1

  | Comb (Or, f1 :: l) ->
      let ll1 = mk_cnf f1 in
      let ll2 = mk_cnf (Comb (Or, l)) in
      List.fold_left 
	(fun acc l1 -> (List.rev_map (fun l2 -> l1 @@ l2)ll2) @@ acc) [] ll1

  | Lit a -> [[a]]
  | Comb (Not, [Lit a]) -> [[Literal.LT.neg a]]
  | _ -> assert false


  let rec unfold mono f = 
    match f with
      | Lit a -> a::mono 
      | Comb (Not, [Lit a]) -> 
	  (Literal.LT.neg a)::mono
      | Comb (Or, l) -> 
	  List.fold_left unfold mono l
      | _ -> assert false
	  
  let rec init monos f = 
    match f with
      | Comb (And, l) -> 
	  List.fold_left init monos l
      | f -> (unfold [] f)::monos
	
  let make_cnf f =
    let sfnc = cnf (sform f) in
    (*Format.eprintf "make_cnf %a@." print sfnc;*)
    init [] sfnc

  (* let make_cnf f = mk_cnf (sform f) *)


end

exception Unsat of int list

let set_cc b = Cc.cc_active := b

let set_arith b =
  Combine.CX.set_arith_active b;
  if b then Cc.cc_active := true

let set_sum = Combine.CX.set_sum_active

module type Solver = sig
  val check_strategy : check_strategy

  val get_time : unit -> float
  val get_calls : unit -> int

  val clear : unit -> unit
  val assume : id:int -> Formula.t -> unit
  val check : unit -> unit

  val entails : Formula.t -> bool
  val push : unit -> unit
  val pop : unit -> unit
  val normalize : Literal.LT.t list -> Literal.LT.t list
end

module Make (Options : sig val profiling : bool end) = struct

  let check_strategy = Eager

  let push_stack = Stack.create ()
  
  let calls = ref 0
  module Time = Timer.Make (Options)

  let get_time = Time.get
  let get_calls () = !calls

  module CSolver = Solver.Make (Options)

  let clear () =
    Stack.clear push_stack;
    CSolver.clear ()

  let check_unsatcore uc =
    eprintf "Unsat Core : @.";
    List.iter 
      (fun c -> 
        eprintf "%a@." (Formula.print_list "or") 
          (List.map (fun x -> Formula.Lit x) c)) uc;
    eprintf "@.";
    try 
      clear ();
      CSolver.assume uc 0;
      CSolver.solve ();
      eprintf "Not an unsat core !!!@.";
      assert false
    with 
      | Solver.Unsat _ -> ();
      | Solver.Sat  -> 
          eprintf "Sat: Not an unsat core !!!@.";
          assert false

  let export_unsatcore cl = 
    let uc = List.map (fun {Solver_types.atoms=atoms} ->
      let l = ref [] in
      for i = 0 to Vec.size atoms - 1 do
        l := (Vec.get atoms i).Solver_types.lit :: !l
      done; 
      !l) cl
    in (* check_unsatcore uc; *)
    uc

  module SInt = 
    Set.Make (struct type t = int let compare = Stdlib.compare end)

  let export_unsatcore2 cl =
    let s = 
      List.fold_left 
        (fun s {Solver_types.name = n} ->
	  try SInt.add (int_of_string n) s with _ -> s) SInt.empty cl
    in 
    SInt.elements s

  let assume ~id f =
    (*Format.eprintf "Assumed f in smt:  %a@." Formula.print f;*)
    Time.start ();
    try
      let cnf = (Formula.make_cnf f) in
      CSolver.assume cnf id;
      Time.pause ()
    with Solver.Unsat ex ->
      Time.pause ();
      raise (Unsat (export_unsatcore2 ex))

  let check () =
    incr calls;
    Time.start ();
    try 
      CSolver.solve ();
      Time.pause ()
    with
      | Solver.Sat -> Time.pause ()
      | Solver.Unsat ex -> 
	  Time.pause ();
	  raise (Unsat (export_unsatcore2 ex))

  let save_state = CSolver.save

  let restore_state = CSolver.restore

  let entails f =
    let st = save_state () in
    let ans = 
      try
        assume ~id:0 (Formula.make Formula.Not [f]) ;
        check ();
        false
      with Unsat _ -> true
    in
    restore_state st;
    ans

  let push () = Stack.push (save_state ()) push_stack

  let pop () = Stack.pop push_stack |> restore_state

  let normalize l (*op*) =
    let nl = CSolver.normalize l  in nl

    (*List.fold_left (fun acc x ->

    let nt1, nt2 = Formula.lit_to_terms x in

    let aa = match Term.view_symbol nt1, Term.view_symbol nt2 with
      | Name (h,_), Name(h1,_) ->
	if Str.string_match (Str.regexp "!k[0-9]*$") (Hstring.view h) 0 ||  Str.string_match (Str.regexp "!k[0-9]*$") (Hstring.view h1) 0 then acc
	else (

    in 
    
    ) nl*)
				  

      

    
end
