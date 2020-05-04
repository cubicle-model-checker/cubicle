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


  let unsolvable _ =  false

  let is_mine_a _ = false

  let is_mine_symb = function (*this*)
    | Sy.Op (Sy.Record | Sy.Access _) -> true
    | _ -> false

  let fully_interpreted _ = false
    
  let type_info = function
    | Record (_,ty) | Access (_,_,ty) | Other (_, ty) -> ty

  let color _ = assert false

  let print fmt m = 
  assert false (*todo*)

  let embed r =
    match X.extract r with
      | Some p -> p
      | None -> Other (r, X.type_info r)
      
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
      | _ , [] -> -1
      |(_, x1)::tl1, (_, x2)::tl2 ->
	let c = raw_compare x1 x2 in
	if c <> 0 then c else raw_compare_list tl1 tl2

	  
  let rec normalize v =
    match v with
      | Record (lbs, ty) ->
	begin
	  let lbs_n = List.map (fun (lb, x) -> lb, normalize x) lbs in
	  match lbs_n with
	    | (lb1, Access(lb2, x, _))::l when Hstring.equal lb1 lb2 ->
	      if List.for_all
		(function
		  | (lb1, Access(lb2, y, _)) ->
		    Hstring.equal lb1 lb2 && compare x y = 0
		  |_ -> false
		) l
	      then x
	      else Record (lbs_n, ty)

	    |_ -> Record (lbs_n, ty)
	end
      | Access (a,x,ty) ->
	begin
	  match normalize x with
	    | Record (lbs, _) -> Hstring.list_assoc a lbs
	    | x_n -> Access (a, x_n, ty)
	end
      | Other _ -> v 

  let embed r =
    match X.extract r with
      | Some p -> p
      | None -> Other(r, X.type_info r)
	
  let compare t u = raw_compare (normalize t) (normalize u)

  (*let compare x y = compare_mine (embed x) (embed y)*)

 

  let is_mine t =
    match normalize t with
      | Other(r, _) -> r
      | x -> X.embed x

  let aux_solve x y =
       if List.mem x (X.leaves y) then raise Unsolvable;
	[x,y]
      
  let solve r1 r2  = 
    match embed r1, embed r2 with
      | Record (l1, _), Record (l2, _) when l1 = l2 -> []
      | Record (l1, _), Record (l2, _) -> assert false
      | Other (a1, _), Other (a2, _) ->
	if X.compare r1 r2 > 0  then [r1,r2] else [r2,r1]
      | Other (a1, _), Record(l2, _) -> aux_solve r1 r2
      | Record (l1, _), Other (a2, _) -> aux_solve r2 r1	
      | Access _, _ -> assert false
      |_, Access _ -> assert false
    
  let leaves t =
    let rec leaves t =
      match normalize t with
	| Record (lbs, _) ->
	  List.fold_left (fun s (_, x) -> XS.union (leaves x) s) XS.empty lbs
	| Access (_, x, _) -> leaves x
	| Other (x, _) -> List.fold_left (fun s x -> XS.add x s) XS.empty (X.leaves x)
    in
    XS.elements (leaves t)
    
    
  let rec hash = function
    | Record (lbs, ty) ->
      List.fold_left 
	(fun h (lb, x) -> 17 * hash x + 13 * Hstring.hash lb + h) 
	(Ty.hash ty) lbs
    | Access (a, x, ty) ->
      19 * hash x + 17 * Hstring.hash a + Ty.hash ty 
    | Other (x, ty) -> 
      Ty.hash ty + 23 * X.hash x


  let subst p v r =
    let rec subst_rec p v = function
      | Other (t, ty) -> embed (if X.compare p t = 0 then v else X.subst p v t)
      | Access (a, t, ty) ->
	Access (a, subst_rec p v t, ty)
      | Record (lbs, ty) ->
	let lbs = List.map (fun (lb, t) -> lb, subst_rec p v t) lbs in
	Record (lbs, ty)		     
    in is_mine (subst_rec p v r)
    


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

  let make t = assert false
   (* let rec make_rec t ctx = 
      let { Term.f = f; xs = xs; ty = ty} = T.view t in
      match f, ty with*)
	(*| Symbols.Op (Symbols.Record), Ty.Trecord {Ty.lbs=lbs} ->
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
	  Record (l, ty), ctx*)
(*	| Symbols.Op (Symbols.Access a), _ ->
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
*)
  module Rel =
  struct
    type r = X.r
    type t = unit

    exception Inconsistent
    let empty _ = ()
    let assume _ _ = (), { assume = []; remove = []}
    let query _ _ = Sig.No (*todo*)
    let case_split env = []
    let add env _ = env
    end

  end
