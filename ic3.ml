open Types
open Ast

exception Unsafe of t_system



module type SigV = sig

  type 'a g
  type t

  (* Universally quanfified conjonction, good*)
  type uconj
  (* Existentially quantified conjonction, bad *)
  type econj

  type res_ref =
    | Bad_Parent
    | Covered of t
    | Extrapolated of t

  val create_uconj : Variable.t list -> Types.SAtom.t -> uconj
  val create_econj : Variable.t list -> Types.SAtom.t -> econj

  val create : uconj -> econj -> (t * transition) list -> t
  val delete_parent : t -> t -> transition -> t
  val add_parent : t -> t -> transition -> t
  val get_parents : t -> (t * transition) list

  (* hashtype signature *)
  val hash : t -> int
  val equal : t -> t -> bool

  (* orderedtype signature *)
  val compare : t -> t -> int

  (* ic3 base functions *)
    
  (* Create a list of nodes from the node
     w.r.t the transitions *)
  val expand : t -> transition list -> transition list 
    
  val refine : t -> t -> transition -> 'a g -> res_ref
  val is_bad : t -> bool
    
end 

module rec Vertice : SigV with type 'a g = 'a G.t = struct
    
  type uconj = Cube.t

  type econj = Cube.t

  type 'a g = 'a G.t
  type t = 
      { 
	good : uconj;
	bad  : econj;
	parents : (t * transition) list;
	id : int;
      }
	
  (* In case we want a hashtable *)
  let hash t = t.id
  let equal t1 t2 = t1.id = t2.id

  (* In case we want a map *)
  let compare t1 t2 = Pervasives.compare t1.id t2.id

  type res_ref =
    | Bad_Parent
    | Covered of t
    | Extrapolated of t

  let create_uconj vl sa = 
    Cube.create vl sa

  let create_econj = create_uconj
    
  let create =
    let cpt = ref 0 in
    fun g b p ->
      incr cpt;
      {
	good = g;
	bad = b;
	parents = p;
	id = !cpt;
      }

  let delete_parent v p tr =
    let l = v.parents in
    let tn = tr.tr_info.tr_name in
    let rec delete acc = function
      | [] -> acc
      | (p', tr')::l when 
	  equal p p' 
	  && Hstring.equal tr'.tr_info.tr_name tn
	  -> List.rev_append acc l
      | c :: l -> delete (c::acc) l
    in 
    let nl = delete [] l in
    {v with parents = nl}

  let add_parent v p tr =
    {v with parents = (p, tr)::v.parents}

  let get_parents v = v.parents

  let pickable v tr =
    failwith "TODO"

  let expand v tl = List.filter (pickable v.good) tl
  let refine v1 v2 = failwith "TODO" 
  let is_bad v = not (SAtom.mem Atom.False v.bad.Cube.litterals)

end

and G : Map.S with type key = Vertice.t = Map.Make(Vertice)



module type SigQ = sig

  type 'a t

  exception Empty

  val create : unit -> 'a t
  val push : 'a -> 'a t -> unit
  val pop : 'a t -> 'a
  val clear : 'a t -> unit
  val copy : 'a t -> 'a t
  val is_empty : 'a t -> bool
  val length : 'a t -> int

  val iter : ('a -> unit) -> 'a t -> unit

end

type result =
  | RSafe
  | RUnsafe
      
module Make 
  ( Q : SigQ ) 
  ( V : SigV with type t = G.key and type 'a g = 'a G.t ) = 
struct
  
  type v = V.t
  type q = V.t Q.t

  let find_graph g v = 
    try G.find v g
    with Not_found -> []

  let add_graph v g =
    let l = find_graph g v in
    G.add v l g

  let add_extra_graph v r g =
    let l = find_graph g v in
    G.add v (r::l) g

  type transitions = transition list

  let search system prop = 
    (* top = (true, unsafe) *)
    (* Create the good formula of top, true *)
    let gtop = V.create_uconj [] SAtom.empty in
    (* Create the bad formula of top, unsafe *)
    let cunsl = system.t_unsafe in
    let cuns =
      match cunsl with
	| [f] -> f
	| _ -> assert false
    in
    let (unsv, unsf) = 
      let c = cuns.cube in (c.Cube.vars, c.Cube.litterals) in
    let btop = V.create_econj unsv unsf in
    (* Create top with gtop, btop and no parents *)
    let top = V.create gtop btop [] in

    (* root = (init, false) *)
    let (initv, initfl) = system.t_init in
    let initf = 
      match initfl with 
	| [f] -> f 
	| _ -> assert false 
    in
    (* Create the good formula of root, init *)
    let groot = V.create_uconj initv initf in
    (* Create the bad formula of root, false *)
    let broot = V.create_econj [] SAtom.empty in
    (* Create root with groot, broot and no parents *)
    let root = V.create groot broot [] in
    (* Working queue of nodes to expand and refine *)
    let todo = Q.create () in
    (* rushby graph *)
    let rgraph = G.singleton top [] in
    let rec refine v1 v2 tr rg =
      Format.eprintf "[Induct] refining %d --%a--> %s@." 
	(V.hash v1) Hstring.print tr.tr_info.tr_name 
	(let n = V.hash v2 in 
	 if n = 1 then "top" else string_of_int n);
      (* In this case we are trying to execute a new transition
	 from v1 but v1 is already bad so must not be considered as
	 a parent node. *)
      if V.is_bad v1 then (
	Format.eprintf 
	  "We discard the treatment of this edge since (%d) is now bad@." (V.hash v1);
	rg
      )
      else if V.is_bad v2 then
	match V.refine v1 v2 tr rg with  
	  (* v1 and tr imply bad *)
	  | V.Bad_Parent -> 
	    (* If v1 is root, we can not refine *)
	    if V.equal v1 root then raise (Unsafe system);
	    (* Else, we recursively call refine on all the parents *)
	    List.fold_left (
	      fun acc (vp, tr) -> refine vp v1 tr acc
	    ) rg (V.get_parents v1)
	  (* The node vc covers v2 by tr *)
	  | V.Covered vc -> 
	    let v2 = V.delete_parent v2 v1 tr in
	    let vc = V.add_parent vc v1 tr in
	    let rg = add_graph v2 (add_graph vc rg) in
	    refine v1 vc tr rg
	  | V.Extrapolated vn -> 
	    let v2 = V.delete_parent v2 v1 tr in
	    let vn = V.add_parent vn v1 tr in
	    let rg = add_extra_graph v2 vn (add_graph vn rg) in
	    Q.push vn todo;
	    rg
      else (
	Format.eprintf "(%d) is safe, no backward refinement@." (V.hash v2);
	rg
      )
    in
    Q.push root todo;
    let transitions = system.t_trans in
    let rec expand rg =
      let v1 = Q.pop todo in
      let trans = V.expand v1 transitions in
      let rg = List.fold_left (
	fun acc tr -> refine v1 top tr acc ) rg trans
      in expand rg
    in
    let _ = 
      try expand rgraph
      with Q.Empty -> Format.eprintf "Empty queue, Safe system@."
    in ()
end

module RG = Make(Queue)(Vertice)
