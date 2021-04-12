open Format
open Sig
open Exception
module Sy = Symbols
module T = Term
module A  = Literal


type ('a, 'b) mine = Yes of 'a | No of 'b

type 'a abstract = 
  | Record of (Hstring.t * 'a abstract) list * Ty.t
  | Access of Hstring.t * 'a abstract * Ty.t
  | Other of 'a * Ty.t

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Make (X : ALIEN) = struct 

  module XS = Set.Make(struct type t = X.r let compare = X.compare end)

  let name = "Records"

  type t = X.r abstract
  type r = X.r

  let unsolvable _ = false

  let is_mind_a _ = false

      
  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
      
    let rec print fmt = function
      | Record (lbs, _) -> 
        fprintf fmt "{";
        let _ = List.fold_left
	  (fun first (lb, e) -> 
	    fprintf fmt "%s%s = %a"
	      (if first then "" else "; ") (Hstring.view lb) print e;
	    false
	  ) true lbs in
        fprintf fmt "}"
      | Access(a, e, _) -> 
        fprintf fmt "%a.%s" print e (Hstring.view a)
      | Other(t, _) -> X.print fmt t

  end
  (*BISECT-IGNORE-END*)

  let print = Debug.print


  let rec raw_compare r1 r2 =
    match r1, r2 with
      | Other (u1, ty1), Other (u2, ty2) -> 
        let c = Ty.compare ty1 ty2 in
        if c <> 0 then c else X.compare u1 u2
      | Other _, _ -> -1
      | _, Other _ -> 1
      | Access (s1, u1, ty1), Access (s2, u2, ty2) ->
        let c = Ty.compare ty1 ty2 in
        if c <> 0 then c 
        else 
	  let c = Hstring.compare s1 s2 in
	  if c <> 0 then c
	  else raw_compare u1 u2
      | Access _, _ -> -1
      | _, Access _ -> 1
      | Record (lbs1, ty1), Record (lbs2, ty2) ->
        let c = Ty.compare ty1 ty2 in
        if c <> 0 then c else raw_compare_list lbs1 lbs2
  and raw_compare_list l1 l2 = 
    match l1, l2 with
      | [], [] -> 0
      | [], _ -> 1
      | _, [] -> -1
      | (_, x1)::l1, (_, x2)::l2 -> 
	let c = raw_compare x1 x2 in 
	if c<>0 then c else raw_compare_list l1 l2
          
  let rec normalize v =
    match v with
      | Record (lbs, ty) ->
	begin
	  let lbs_n = List.map (fun (lb, x) -> lb, normalize x) lbs in
	  match lbs_n with
	    | (lb1, Access(lb2, x, _)) :: l when Hstring.equal lb1 lb2 ->
	      if List.for_all 
		(function 
		  | (lb1, Access(lb2, y, _)) -> 
		    Hstring.equal lb1 lb2 && raw_compare x y = 0
		  | _ -> false) l 
	      then x 
	      else  Record (lbs_n, ty) 
	    | _ -> Record (lbs_n, ty)
	end
      | Access (a, x, ty) ->
	let n = normalize x in
	begin
	  match n with
	    | Record([],_) -> v
	    | Record (lbs, _) -> Hstring.list_assoc a lbs 
	    | x_n -> Access (a, x_n, ty)
	end
      | Other _ -> v

  let embed r =
    match X.extract r with
      | Some p -> p
      | None -> Other(r, X.type_info r)

  let compare_mine t u = raw_compare (normalize t) (normalize u)
    
  let compare x y = compare_mine (*(embed x) (embed y)*) x y 

  let is_mine t =
    match normalize t with
      | Other(r, _) -> r
      | x -> X.embed x

  let type_info t =
    match t with 
    | Record (_, ty) | Access (_, _, ty) | Other (_, ty) -> ty

  let make t =
    let rec make_rec t ctx =
      let { T.f = f; xs = xs; ty = ty} = T.view t in
      match f, ty with
	| Symbols.Op (Symbols.Record), Ty.Trecord {Ty.name = name;Ty.lbs=lbs} ->
	  if xs = [] then Record([],ty), []
	  else
	    begin
	      assert (List.length xs = List.length lbs);
	      let l, ctx = 
		List.fold_right2 
		  (fun x (lb, _) (l, ctx) -> 
		    let r, ctx = make_rec x ctx in 
                    let tyr = type_info r in
		    let dlb = T.make (Symbols.Op (Symbols.Access lb)) [t] tyr in
		    let c = Literal.LT.make (Literal.Eq (dlb, dlb)) in
		    (lb, r)::l, c::ctx
		  ) 
		  xs lbs ([], ctx)
	      in
	      Record (l, ty), ctx
	    end
	| Symbols.Op (Symbols.Access a), _ ->
	  begin
	    match xs with
	      | [x] -> 
		let r, ctx = make_rec x ctx in
		Access (a, r, ty), ctx
	      | _ -> assert false
	  end

	| _, _ -> 
	  let r, ctx' = X.make t in
	  Other (r, ty), ctx'@ctx
    in
    let r, ctx = make_rec t [] in
    let is_m = is_mine (normalize r) in
    is_m, ctx

  let color _ = assert false
    
  let embed r =
    match X.extract r with
      | Some p -> p
      | None -> Other(r, X.type_info r)

  let xs_of_list = List.fold_left (fun s x -> XS.add x s) XS.empty

  let leaves t = 
    let rec leaves t = 
      match normalize t with
	| Record (lbs, _) -> 
	  List.fold_left (fun s (_, x) -> XS.union (leaves x) s) XS.empty lbs
	| Access (_, x, _) -> leaves x
	| Other (x, _) -> xs_of_list (X.leaves x)
    in
    XS.elements (leaves t)

  let rec hash  = function
    | Record (lbs, ty) ->
      List.fold_left 
	(fun h (lb, x) -> 17 * hash x + 13 * Hstring.hash lb + h) 
	(Ty.hash ty) lbs
    | Access (a, x, ty) ->
      19 * hash x + 17 * Hstring.hash a + Ty.hash ty 
    | Other (x, ty) -> 
      Ty.hash ty + 23 * X.hash x

  let rec subst_rec p v r = 
    match r with
      | Other (t, ty) -> 
	embed (if X.compare p t = 0 then v else X.subst p v t)
      | Access (a, t, ty) ->
	Access (a, subst_rec p v t, ty)
      | Record (lbs, ty) ->
	let lbs = List.map (fun (lb, t) -> lb, subst_rec p v t) lbs in
	Record (lbs, ty)

  let subst p v r = is_mine (subst_rec p v r)
    
  let is_mine_symb =  function 
    | Symbols.Op (Symbols.Record | Symbols.Access _) -> true
    | _ -> false

  let fresh_string = 
    let cpt = ref 0 in
    fun () ->
      incr cpt;
      "!k" ^ (string_of_int !cpt)
	
  let fresh_name ty = T.make (Sy.name (Hstring.make (fresh_string()))) [] ty


  (* Shostak'pair solver adapted to records *)

  let mk_fresh_record x info = 
    let ty = type_info x in
    let lbs = match ty with Ty.Trecord r -> r.Ty.lbs | _ -> assert false in
    let lbs = 
      List.map 
	(fun (lb, ty) -> 
	  match info with
	    | Some (a, v) when Hstring.equal lb a ->	      
	      lb, v 
	    | _ -> let n = embed (X.term_embed (fresh_name ty)) in lb, n)
	lbs
    in
    Record (lbs, ty), lbs

  let rec occurs x = function
    | Record (lbs, _) ->
      List.exists (fun (_, v) -> occurs x v) lbs
    | Access (_, v, _) -> occurs x v
    | Other _ as v -> compare_mine x v = 0 (* XXX *)

  let direct_args_of_labels x = List.exists (fun (_, y)-> compare_mine x y = 0)

  let rec subst_access x s e = 
    match e with
      | Record (lbs, ty) ->
	  Record (List.map (fun (n,e') -> n, subst_access x s e') lbs, ty)
	 	    
      | Access (lb, e', _) when compare_mine x e' = 0 -> 
	Hstring.list_assoc lb s
      | Access (lb', e', ty) -> Access (lb', subst_access x s e', ty)
      | Other _ -> e

  let rec find_list x = function
    | [] -> raise Not_found
    | (y, t) :: _ when compare_mine x y = 0 -> t
    | _ :: l -> find_list x l

  let split l = 
    let rec split_rec acc = function
      | [] -> acc, []
      | ((x, t) as v) :: l -> 
	try acc, (t, find_list x acc) :: l 
	with Not_found -> split_rec (v::acc) l
    in
    split_rec [] l

  let fully_interpreted _ = false

  let rec term_extract r =
    match X.extract r with
      | Some v -> begin match v with
	  | Record (lbs, ty) -> 
	    begin try
		    let lbs = 
		      List.map 
		        (fun (_, r) -> 
		          match term_extract (is_mine r) with 
			    | None -> raise Not_found
			    | Some t -> t) lbs in
		    Some (T.make (Symbols.Op Symbols.Record) lbs ty)
	      with Not_found -> None
	    end
	  | Access (a, r, ty) ->
	    begin
	      match X.term_extract (is_mine r) with
		| None -> None
		| Some t -> 
		  Some (T.make (Symbols.Op (Symbols.Access a)) [t] ty)
	    end
	  | Other (r, _) -> X.term_extract r
      end
      | None -> X.term_extract r

        
  let orient_solved p v pb = 
    if List.mem p (X.leaves v) then raise Exception.Unsolvable;
    { pb with sbt = (p,v) :: pb.sbt }
      
(*  let solve r1 r2 pb = 
    match embed r1, embed r2 with
      | Record (l1, _), Record (l2, _) -> 
        let eqs = 
          List.fold_left2 
            (fun eqs (a,b) (x,y) ->
              assert (Hstring.compare a x = 0);
              (is_mine y, is_mine b) :: eqs
            )pb.eqs l1 l2
        in
        {pb with eqs=eqs}
          
      | Other (a1,_), Other (a2,_)    -> 
        if X.compare r1 r2 > 0 then { pb with sbt = (r1,r2)::pb.sbt }
        else { pb with sbt = (r2,r1)::pb.sbt }

      | Other (a1,_), Record (l2, _)  -> orient_solved r1 r2 pb
      | Record (l1, _), Other (a2,_)  -> orient_solved r2 r1 pb
      | Access _ , _ -> assert false
    | _ , Access _ -> assert false*)

  let rec solve_one u v =
    if compare_mine u v = 0 then [] else
      match u, v with
	| Access (a, x, _), v | v, Access (a, x, _) ->
	  let nr, _ = mk_fresh_record x (Some(a,v)) in
	  solve_one x nr
	(*| Record([],_), Record([],_) -> []
	| (Record([],_)as y), x | x, (Record([],_) as y) ->
	   begin
	  match x with
	    | Other _ -> [x,y]
	    | Record _ -> raise Exception.Unsolvable
	    | Access _ -> [x,y]
	    end*)
	| Record (lbs1, _), Record (lbs2, _) ->
	  begin
	    try 
	      let l = 
		List.fold_left2 
		  (fun l (_, x) (_, y) -> (solve_one x y)@l) [] lbs1 lbs2
	      in 
	      resolve l
	    with Invalid_argument _ -> raise Exception.Unsolvable
	  end

	| (Record (lbs, _) as w), (Other _ as x) 
	| (Other _ as x), (Record (lbs, _) as w) ->
	    if not (occurs x w) then [x, w]
	    else if direct_args_of_labels x lbs then raise Exception.Unsolvable
	    else 
	      let nr, sigma = mk_fresh_record w None in
	      let l = 
		List.fold_left2
		  (fun l (_, ai) (_, ei) -> 
		     (solve_one ai (subst_access x sigma ei))@l) [] sigma lbs
	      in
	      (x, nr)::resolve l

	| Other _, Other _ -> [u, v]
	    
  and resolve l = 
    let s, r = split l in
    match r with [] -> s | (u, v) :: l -> resolve (s@(solve_one u v)@l)

  let solve r1 r2 =
    let r1 = normalize (embed r1) in
    let r2 = normalize (embed r2) in
    List.map (fun (x, y) -> is_mine x, is_mine y) (solve_one r1 r2)


  module Rel =
  struct
    type r = X.r
    (*type t = unit

    let empty _ = ()*)
   exception Inconsistent
    exception Done of X.r   * X.r 



   module Ex = Explanation

     
    module MX = Map.Make(struct type t = X.r include X end)
    module XRS = Set.Make (struct type t = X.r * Ex.t  let compare (x,_) (y,_) = X.compare x y end)
    module EQS = Set.Make (struct type t = X.r let compare = X.compare end)
    module CANDIDATES = Set.Make (struct type t = bool * X.r * X.r let compare (_,x,_) (_,y,_) = X.compare x y end)

    type t = (XRS.t * EQS.t * CANDIDATES.t option) MX.t 

    let empty _ = MX.empty


    let fields_of t =
      match t with
	| Ty.Trecord { lbs = lbs} ->
	  Some lbs 
       (*Some lbs*)
	  (*Some (List.fold_left (fun acc lbl -> HSS.add lbl acc) HSS.empty lbs)*)
	| _ -> None

	  
    let is_ground t =
      
	  let term = X.term_extract t in
	    match term with
	      | Some s -> let sy = (T.view s).f in
			  begin
			    match sy with
			      | Name _ | Int _ | Real _ -> true
			      
			      | _ -> false
			  end 
	      | None -> false


    let rec assoc_snd_xr l1 l2 v =
      match l1, l2 with
	| [], [] -> None
	| (a,b)::tl, (c,d)::tl2 ->
	  if X.compare v b = 0 then Some (a,true)
	  else if X.compare v d = 0 then Some (b,false)
	  else assoc_snd_xr tl tl2 v
	| _ -> assert false


(*Record of (Hstring.t * 'a abstract) list * Ty.t
  | Access of Hstring.t * 'a abstract * Ty.t
  | Other of 'a * Ty.t

*)
    exception Clean 
      (*---DUPLICATE CUBICLE---*)
    let assume env la =
      let env, neqs, remove =
	List.fold_left(
	  fun (env,neqs, remove) l->
	    match l with 
	      | A.Distinct(false, [r1;r2 ]), _, ex-> 
		begin
		  match embed r1, embed r2 with
		    | Record ([],_), x | x, Record ([],_) -> 


		      env, neqs, remove
		    | Record (rf1,ty1), Record(rf2,ty2) ->
		      let flag, (ineqs, eqs, candidates), left, right =
			try true, MX.find r1 env, r1, r2  with Not_found -> (* maybe the other record already exists in the table *)
			  try true, MX.find r2 env, r2, r1  with Not_found ->
			    let candidates =
			      CANDIDATES.of_list(
				List.fold_left2 (fun acc (_, val1) (_, val2)  ->
				  if (is_ground (is_mine val1) && is_ground (is_mine val2)) then acc else
				  (false, is_mine val1, is_mine val2 )::acc)[] rf1 rf2
			      )
			    in
			    false, (XRS.add (r2,ex) XRS.empty, EQS.empty, Some candidates), r1, r2 (* r1 -> (ineqs: r2 AND eqs: nothing) *)
		      in
		      let candidates =
			begin
			match candidates with
			  | None -> candidates
			  | Some s ->
			    
			    if flag then
			      begin
				Some (CANDIDATES.filter ( fun (sign, lel, rel) ->
				  if sign then
				    begin
				      try 
					let rec aux rl1 rl2  =
					  match rl1, rl2 with
					    | [], [] -> true
					    | (_,v1)::tl1, (_,v2)::tl2 ->
					      let v1 = is_mine v1 in
					      let v2 = is_mine v2 in
					      if (X.compare v1 lel = 0 && X.compare v2 rel = 0) || (X.compare v1 rel = 0 && X.compare v2 lel = 0) then raise Clean
					      else aux tl1 tl2
					    | _ -> assert false
					in aux rf1 rf2
				      with Clean -> false
				    end
						
				  else true

				) s )
			      
			      end 
			    else candidates
			end 
		      in 
			 
		      
		      let env = MX.add left (XRS.add (right,ex) ineqs, eqs,  candidates) env in

		      env, neqs, remove	
			
		    | ((Other(el,_)) as x), re  | re, ((Other (el,_)) as x)-> 
		      (* split according to what re is *)
		      (* todo? break into different cases instead of match inside match -> don't really repeat cod*)
		      begin
			match re with
			  | Record (r,t) ->
			    begin
			      let ineqs, other_eqs, cand =
				try MX.find (is_mine x) env
				with Not_found -> XRS.add ((is_mine re),Ex.empty) XRS.empty, EQS.empty, None in
			      let env = MX.add (is_mine x) (XRS.add (is_mine re, ex) ineqs, other_eqs, cand) env in
			      begin
			      match fields_of t with
				| None -> assert false
				| Some [(hs,ty)] ->
				    (* if there is only one field, then you can go from a record to an access *)
				    let xa = is_mine (Access (hs,  x, ty)) in
				    let v = is_mine (Hstring.list_assoc hs r) in
				    (*check MX if there's other definitions already*)
				    let poss_xa, xa_eqs, xa_cand = try MX.find xa env 
				      with Not_found -> (XRS.add (v, Ex.empty) XRS.empty), EQS.empty, None in
				    (*let ex = Ex.union ex_xa ex in *) 
				    let env = MX.add xa (XRS.add (v,Ex.empty) poss_xa, xa_eqs, xa_cand) env in
				    let d = A.Distinct(false,[xa; v]) in
				    env, (LSem d, ex)::neqs, remove
				      
				| Some _ ->
		   		    (* add X != re to MX [adding re to the possible ineqs returned earlier *)
				    env, neqs, remove
			      end
			    end   
			  | Access (field, record, ty_rec) ->
			    let ineqs, acc_eqs, acc_cand =
			      try MX.find (is_mine re) env
			      with Not_found -> XRS.add ((is_mine x),Ex.empty) XRS.empty, EQS.empty, None in
			      (* check if access field's parent record is already in MX *)
			      (* if it is, return true and the set of inequalities *)
			      (* else false and an empty set *)
			    let parent_rec = is_mine record in
			    let clean, (rec_ineqs, rec_eqset, parent_cand) =
			      try true, MX.find parent_rec env
			      with Not_found -> false, (XRS.empty, EQS.empty, None) in
			      (* if there was already stuff in MX, check it to remove 
				 anything redundant *)
			    let env = MX.add (is_mine re) (XRS.add (is_mine x, ex) ineqs, rec_eqset, acc_cand ) env in
			      (*let neq = A.Distinct(false,[is_mine re; is_mine x]) in*)
			    if clean then
			      begin
				let temp =
				    (* remove from inequalites everything 
				       that has a field equal to the current access
				       field's value *)
				  XRS.filter (fun (elx,_) ->
				    match embed elx with
				      | Record (r_xrs,_) ->
					let hs = Hstring.list_assoc field r_xrs in
					X.compare (is_mine hs) el <> 0 
				      | _ -> true) rec_ineqs
				in
				  (* re-map parent to new values  *)
				let env = MX.add parent_rec (temp,EQS.empty, parent_cand) env in
				env, neqs, remove
			      end
			    else env, neqs, remove
			  | Other(el2, _) -> 
			    let env =
			      MX.mapi (fun r (ineqs, eqs, candidates) ->
				match embed r with 
				  | Record (rfv, _) ->
				    begin
				      match candidates with
					| None -> ineqs, eqs, candidates
					| Some s ->
					  let cand =
					    CANDIDATES.filter (fun (sign, left, right) ->
					      
					      if sign then
						not ((X.compare left el = 0 && X.compare right el2 = 0) || (X.compare left el2 = 0 && X.compare right el = 0))
					      else true) s
					  in
					  ineqs, eqs, Some cand
				    end
				  | _ -> ineqs, eqs, candidates
			      ) env in 

			    env, neqs, remove
		      end  			
			
		    | ((Record (r,t)) as re), ((Access (field, record, ty_re)) as ac )
		    | ((Access (field,record,ty_re)) as ac), ((Record (r,t)) as re)  -> 
		    (*X.c != { a = 2; b = 3 OR {a = 2; b = 3 } != X.c *)
		      (* mix the two previous: rec and access*)
		      (**)
		      let my_x = is_mine ac in		      
		      (*check if access in MX*)
		      let acc_ineqs, acc_eqset,acc_cand = try MX.find my_x  env
			with Not_found -> XRS.add (is_mine re, Ex.empty) XRS.empty, EQS.empty, None in
		      
		      (* add record to MX as inequality for access *)
		      let env = MX.add my_x (XRS.add (is_mine re, ex) acc_ineqs, acc_eqset, acc_cand) env in
		      
		      let clean, (rec_ineqs,rec_eqset,cand) =
			try true, MX.find (is_mine record) env
			with Not_found -> false, (XRS.empty, EQS.empty, None) in
		      let neqs, env =
			if clean then
			  begin
			    let temp =
			      XRS.filter (fun (elx,_) ->
				match embed elx with
				  | Record (r_xrs,_) ->
				    X.compare (is_mine(Hstring.list_assoc field r_xrs)) (is_mine re) <> 0 
				  | _ -> true) rec_ineqs
			    in
			    let env = MX.add (is_mine record) (temp, rec_eqset, cand) env
			    in neqs, env 
			  end
			else neqs, env
		      in 
							  
		      begin
			match fields_of t with
			  | None -> assert false
			  | Some [(hs,ty)] ->
			    let xa = is_mine (Access (hs,  re, ty)) in
			    let v = is_mine (Hstring.list_assoc hs r) in
			    let poss_xa, eqset_xa,xa_cand = try MX.find xa env 
			      with Not_found -> (XRS.add (v, Ex.empty) XRS.empty), EQS.empty, None in
			    let env = MX.add xa (XRS.add (v,Ex.empty) poss_xa, eqset_xa, xa_cand) env in
			    (*let d = A.Distinct(false,[xa; v]) in	*)    
			    env, (*(LSem d, ex)::*)neqs, remove
			  | Some lbs -> env, neqs, remove
			    
		      end 
			
		    | _ -> env, neqs, remove (* access != access *)
		end

	      | A.Eq(r1,r2),_, ex->

		begin
		  match embed r1, embed r2 with
		    | (Record ([],_) as re),  ((Other (el, el_ty)) as x)
		    | ((Other (el, el_ty)) as x), (Record ([],_) as re) -> 
		      let ineqs, eqs, cand =
			try MX.find (is_mine x) env with
			    Not_found -> XRS.empty, EQS.empty, None in
		      let ineqs =
			XRS.filter (fun (neq, _) -> X.compare (is_mine x) neq <> 0) ineqs
		      in
		      let eqs = EQS.add (is_mine re) eqs in
		      let env = MX.add (is_mine x) (ineqs, eqs, cand) env
		      in env, neqs, remove 
			
		      
		    | re, ((Other (el, el_ty)) as x)
		    | ((Other (el, el_ty)) as x), re ->
		      begin
			match re with
			  | Access _ -> 
			    begin
			      let ineqs, eqs, cand = 
				try
				  MX.find (is_mine re) env
				with Not_found -> XRS.empty, EQS.empty, None
			      in
			      let eq = EQS.add (is_mine x) eqs in
			      (*check the potential inequalities to remove anything that corresponds to 
				current equality *)
			      let ineqs =
				XRS.filter (fun (neq, _) -> X.compare (is_mine x) neq <> 0) ineqs in
			      let env = MX.add (is_mine re) (ineqs,eq, cand) env in 
			      (*let d = A.Eq(r1, r2)
			      in*)
			      env, (*(LSem d, ex)::*)neqs, remove
			    end
			  | Record (rr, rrty) -> 
			    let ineqs, eqs,cand =
			      try MX.find (is_mine x) env with
				  Not_found -> XRS.empty, EQS.empty, None in
			    let ineqs =
			      XRS.filter (fun (neq, _ ) -> X.compare (is_mine x) neq <> 0) ineqs
			    in
			    let eqs = EQS.add (is_mine re) eqs in
			    let env = MX.add (is_mine x) (ineqs, eqs, cand) env (*in
			    let neqs =
			      List.fold_left ( fun acc (field, value)  ->
				let value = is_mine value in
				let fv = is_mine (Access (field, x, el_ty)) in
				(LSem (A.Eq(fv, value)), ex)::acc
			      ) neqs rr*)
			    in env, neqs, remove
			  | Other (el2, _) ->
  			    let env =
			      MX.mapi (fun r (ineqs, eqs, candidates)  ->
				match embed r with
				  | Record (rl, rty) ->
				    begin (*cand match*)
				      match candidates with
					| None -> ineqs, eqs, candidates
					| Some s ->
					  let cand =

					    CANDIDATES.filter (fun (sign, left, right) ->
					      if not sign then 
						not ((X.compare left el = 0 && X.compare right el2 = 0) || 
							(X.compare left el2 = 0 && X.compare right el = 0))
					      else true ) s in 
					    
					    (*CANDIDATES.fold ( fun (sign, left, right) acc ->
					      if sign then CANDIDATES.add (sign, left, right) acc
					      else
						if (X.compare left el = 0 && X.compare right el2 = 0) || 
						  (X.compare left el2 = 0 && X.compare right el = 0)
						then acc
						else CANDIDATES.add (sign, left, right) acc
					      ) s CANDIDATES.empty in*)
					  ineqs, eqs, Some cand
				    end (*cand match *)

				      
				      
				    
				  | _ -> ineqs, eqs, None) env
			    in
			    env, neqs, remove
		      end 
			
		    | Access (field1, record1, ty_r1), Access (field2, record2, ty_r2) ->
		      begin
			try
			  let (ineqs1, eqs1,c1), (ineqs2, eqs2,c2) =
			    MX.find r1 env , MX.find r2 env
			  in
			  let eqs = EQS.union eqs1 eqs2 in
			  let ineqs = XRS.union ineqs1 ineqs2 in
			  let env = MX.add r1 (ineqs,eqs, c1) env in
			  let env = MX.add r2 (ineqs, eqs,c2) env in
			  env, neqs, remove
			with Not_found -> env, neqs, remove
		      end
		    | ((Access (field, record, ty) as ac)), ((Record(rfs, rty) as ar)) | ((Record (rfs,ty) as ar)), ((Access (field, record, rty) as ac)) ->

		      begin
			try
			  let ineqs, eqs,_ =
			    MX.find (is_mine ac) env
			  in
			  let ineqs =
			    XRS.filter (fun (neq, _) -> X.compare (is_mine ar) neq <> 0) ineqs
			  in
			  let eqs = EQS.add (is_mine ar) eqs in
			  let env = MX.add (is_mine ac) (ineqs,eqs,None) env in
			  env, neqs, remove
			with Not_found -> env, neqs, remove
		      end
			
		    | Record (rfv1, rty1), Record (rfv2, rty2) ->
		      (*let neqs =
			List.fold_left2 (fun acc (_, v1) (_, v2) ->
			  let d = A.Eq(is_mine v1, is_mine v2) in
			  (LSem d, ex)::acc) neqs rfv1 rfv2 in *)
		      let flag, (ineqs, eqs, cands), left, right =
			try true, MX.find r1 env, r1, r2 with
			    Not_found ->
			      try true, MX.find r2 env, r2, r1 with
				  Not_found ->
				   false, (XRS.empty, (EQS.add r2 EQS.empty), None), r1, r2
		      in
		      if flag then
			let ineqs = XRS.filter (fun (neq, _) -> X.compare right neq <> 0) ineqs
			in
			let eqs = EQS.add right eqs in
			let env = MX.add left (ineqs, eqs, cands) env in
			env, neqs, remove
		      else 
		      env, neqs, remove
			

		end 
	      | _ -> env,neqs,remove
	    
	    
	)(env,[],[]) la in
		   
      
		env, { assume = neqs; remove = remove}
		  

   
		  
    let query _ _  = Sig.No


    let choose_case r xr env lbs_length acc ty =

      let chosen =
	try XRS.choose xr
	with
	    Not_found -> assert false
      in
      let r = embed r in 
      let emb_chosen = embed (fst chosen) in
      begin (*3*)
	match emb_chosen with
	  | Record (re_chosen, ty_chosen) ->
	    begin (*4*)
	      try
		List.fold_right (fun (field, f_ty) acc1 ->
		  let temp = Access (field, r, ty) in
		  let value = Hstring.list_assoc field re_chosen in
		  let my_temp = is_mine temp in
		  (*Format.eprintf "temp: %a@." X.print my_temp;*)

		  let flag, (_,equalities,_) =
		    try true,
		      MX.find my_temp env
		    with Not_found -> false, (XRS.add ((is_mine value), Ex.empty) XRS.empty, EQS.empty, None)
		  in
		  if flag && not (EQS.is_empty equalities) then
		    begin (*5*) 
		      let values =
			EQS.filter (fun elx ->
			  X.compare (is_mine (Hstring.list_assoc field re_chosen)) elx =  0 ) equalities
		      in
		      if EQS.is_empty values then
			Some (lbs_length, my_temp, is_mine value)
		      else acc 
		    end (*5*)
		  else raise (Done (my_temp, is_mine value))					      
		) re_chosen acc
	      with Done (x,v) -> Some (lbs_length, x, v)
	    end (*4*)
	  | _ -> assert false (*you can't technically end up here since case-splitting is only on things mapped to records*)
      end (*3*)
	

      
      
    let case_split env =
     let acc = MX.fold
	( fun r (xr,_,cands) acc ->
		  match embed r with
		    | Other (_, ty) -> 
		      begin (*1*)
			match ty with
			  | Ty.Trecord {name = name; lbs = lbs } ->
			    let lbs_length = List.length lbs in 
			    if lbs_length = 1 then acc
			    else
			      begin (*1.5*)
			      match acc with
				| Some (n,r,el) when n <= lbs_length ->  acc
				| _ -> if XRS.cardinal xr > 0 then choose_case r xr env lbs_length acc ty else acc (*THIS*)
				  
				  (*--------*)(*------*)
				    
			      end (*1.5*)
			  | _ -> assert false (*other Ty.type cases -- assert false because technically nothing other than record types should be map keys*)
		      end (*1*)
		    | Access (field, accrec, ty) ->
		      begin
			match X.type_info (is_mine accrec) with
			  | Ty.Trecord {lbs = lbs } ->
			    let fty = Hstring.list_assoc field lbs in
			    let lbs_length = List.length lbs in
			    if lbs_length = 1 then acc else 
			      begin
				match fty with
				  | Trecord _  ->
				    choose_case r xr env lbs_length acc ty
				  | _ -> acc
			      end
			  | _ -> acc
			    
		      end
		    | Record _ -> 
		      begin (* cand begin*)
			match cands with
			  | None -> acc
			  | Some s ->
			    let len = CANDIDATES.cardinal s in
			    begin
			      match acc with
				| Some(n,_,_) when n <= len -> acc
				| _ -> 
				  try
				    let _, left, right = CANDIDATES.find_first (fun (sign, left , right ) ->
				      let igl = is_ground left in
				      let igr = is_ground right in
				      Format.eprintf "sign %b igl %b igr %b@." sign igl igr; 
				      not (is_ground left || is_ground right) && not sign ) s
				    in
				    Format.eprintf "from here %a %a?@." X.print left X.print right;
				    Some(len, left, right)
				  with Not_found -> acc
				      
			    end 
		      end (* cand end *)
		      
	) env None
     in
     match acc with
       | None -> []
       | Some (n, xfield, proposed) -> 
	 (*Format.eprintf "proposed casesplit: %a != %a@." X.print xfield X.print proposed;*)
	 [A.Distinct(false, [xfield;proposed]), Ex.empty, Num.Int n]


      
    let add env r = env
     (* if MX.mem r env then env
      else
	match embed r with
	  | Record _ | Access _ ->  MX.add r (XRS.empty, EQS.empty, Some CANDIDATES.empty) env
	  | Other _ ->
	    (match X.type_info r  with
	      |  Ty.Trecord _  ->  MX.add r (XRS.empty, EQS.empty, Some CANDIDATES.empty) env
	      | _ -> env)*)

      
    let print_model _ _ _ = ()
    let new_terms env = T.Set.empty
  end
end
