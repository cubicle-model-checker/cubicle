
type value = 
  | Int of int 
  | Proc of int

(* Module to manage multi-dimensional arrays *)
module type DA = sig
    
  type 'a t
    
  type 'a dima

  val init : int -> int -> 'a -> 'a dima
  val get : 'a dima -> int list -> 'a
  val set : 'a dima -> int list -> 'a -> unit
    
end 

module DimArray : DA = struct
    
  type 'a t = 
    | Arr of 'a array 
    | Mat of 'a t array

  type 'a dima = {dim:int; darr:'a t}

  let init d nb_elem v =
    let darr = 
      let rec init' d nb_elem v =
	match d with
	  | 1 -> Arr (Array.init nb_elem (fun _ -> v))
	  | n -> Mat (Array.init nb_elem (fun _ -> (init' (n-1) nb_elem v)))
      in init' d nb_elem v
    in {dim=d; darr=darr}

  let get t ind = 
    let rec get' t ind =
      match t, ind with 
	| Arr a, [i] -> a.(i) 
	| Mat m, hd::tl -> let t = m.(hd) in get' t tl 
	| _ -> failwith "Index error in Arr module, get"
    in get' t.darr ind

  let set t ind v =
    let rec set' t ind =
      match t, ind with
	| Arr a, [i] -> a.(i) <- v
	| Mat m, hd::tl -> let t = m.(hd) in set' t tl
	| _ -> failwith "Index error in Arr module, set"
    in set' t.darr ind
end

module type St = sig

  type 'a t
  type 'a da
    
  val init : unit -> 'a t
    
  val equal : 'a t -> 'a t -> bool
  val hash : 'a t -> int
    
  val get_v : 'a t -> Hstring.t -> 'a
  val get_a : 'a t -> Hstring.t -> 'a da
  val get_e : 'a t -> Hstring.t -> int list -> 'a
    
  val set_v : 'a t -> Hstring.t -> 'a -> unit
  val set_a : 'a t -> Hstring.t -> 'a da -> unit
  val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
    
  val copy : 'a t -> 'a t
    
end

module State ( A : DA ) : St with type 'a da = 'a A.dima = struct
    
  type 'a t = {globs: (Hstring.t, 'a) Hashtbl.t; arrs: (Hstring.t, 'a A.dima) Hashtbl.t}
  type 'a da = 'a A.dima

  let init () = {globs = Hashtbl.create 17; arrs = Hashtbl.create 17}

  let equal s1 s2 =
    try
      let gs1 = s1.globs in
      let gs2 = s2.globs in
      Hashtbl.iter (
	fun g v1 -> let v2 = Hashtbl.find gs2 g in
		    if v1 <> v2 then raise Exit
      ) gs1;
      true
    with
	Exit -> false

  let hash = Hashtbl.hash

  let get_v t h = Hashtbl.find t.globs h
  let get_a t h = Hashtbl.find t.arrs h
  let get_e t h pl = let arr = get_a t h in
		     A.get arr pl

  let set_v t h v = Hashtbl.replace t.globs h v
  let set_a t h arr = Hashtbl.replace t.arrs h arr
  let set_e t h pl v = let arr = get_a t h in
		       A.set arr pl v

  let copy t = {globs = Hashtbl.copy t.globs; arrs = Hashtbl.copy t.arrs}

end


module type Sys = sig
type 'a s
  type 'a da
  type 'a t = {old_s:'a s; new_s:'a s}
  

  val init : unit -> 'a t

  val get_v : 'a t -> Hstring.t -> 'a
  val get_a : 'a t -> Hstring.t -> 'a da
  val get_e : 'a t -> Hstring.t -> int list -> 'a

  val set_v : 'a t -> Hstring.t -> 'a -> unit
  val set_a : 'a t -> Hstring.t -> 'a da -> unit
  val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit

  val update_s : 'a t -> 'a s -> 'a t

end

module System ( S : St ) : Sys with type 'a da = 'a S.da and type 'a s = 'a S.t = struct

  type 'a t = {old_s:'a S.t; new_s:'a S.t}
  type 'a da = 'a S.da
  type 'a s = 'a S.t

  let init () = {old_s = S.init (); new_s = S.init ()}

  let get_v s h = let state = s.old_s in
		  S.get_v state h
  let get_a s h = let state = s.old_s in
  		  S.get_a state h
  let get_e s h pl = let arrs = s.old_s in
  		     S.get_e arrs h pl

  let set_v s h v = let globs = s.new_s in
  		    S.set_v globs h v
  let set_a s h a = let arrs = s.new_s in
  		    S.set_a arrs h a
  let set_e s h pl v = let arrs = s.new_s in
  		       S.set_e arrs h pl v

  let update_s s ns = {old_s = s.new_s; new_s = ns}

end

module Etat = State (DimArray)
module Syst = System (Etat)

let system = Syst.init ()

let system2 = Syst.init ()

 let arr = DimArray.init 1 4 (Int 0)
 let arr2 = DimArray.init 1 4 0

let () =
  Syst.set_a system (Hstring.make "test") arr;
  Syst.set_a system2 (Hstring.make "test") arr2;
  let a = system.Syst.old_s in ()
