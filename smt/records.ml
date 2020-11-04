open Format
open Sig
open Exception
module Sy = Symbols
module T = Term

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
	begin 
	  match normalize x with 
	    | Record (lbs, _) ->  Format.eprintf "The record in rec.ml %s@."(Hstring.view a);
	      List.iter (fun (x,y) ->Format.eprintf "Record.ml %s field %s@." (Hstring.view a) (Hstring.view x)) lbs;
	      (try Hstring.list_assoc a lbs with Not_found -> assert false)
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

  let type_info = function
    | Record (_, ty) | Access (_, _, ty) | Other (_, ty) -> ty

  let make t = 
    let rec make_rec t ctx = 
      let { T.f = f; xs = xs; ty = ty} = T.view t in
      match f, ty with
	| Symbols.Op (Symbols.Record), Ty.Trecord {Ty.lbs=lbs} ->
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
    let is_m = is_mine r in
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
	    | Some (a, v) when Hstring.equal lb a -> lb, v 
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

	| Record (lbs1, _), Record (lbs2, _) ->
	    let l = 
	      List.fold_left2 
		(fun l (_, x) (_, y) -> (solve_one x y)@l) [] lbs1 lbs2
	    in 
	    resolve l

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
    type t = unit
    exception Inconsistent    
    let empty _ = ()
    let assume _ _ = 
      (), { assume = []; remove = []}
    let query _ _  = Sig.No
    let case_split env = []
    let add env _ = env
    let print_model _ _ _ = ()
    let new_terms env = T.Set.empty
  end
end
