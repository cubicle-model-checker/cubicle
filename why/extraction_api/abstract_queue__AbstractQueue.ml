(* This file has been generated from Why3 module AbstractQueue *)

type f = Fol__FOL.t

(*-----------------  Begin manually edited ------------------*)
let compare_f f1 f2 =
      let v1 = Fol__FOL.size f1 in
      let v2 = Fol__FOL.size f2 in
      let c = Pervasives.compare v1 v2 in
      if c <> 0 then c else
        let c1 = Fol__FOL.card f1 in
        let c2 = Fol__FOL.card f2 in
        let c = Pervasives.compare c1 c2 in
        if c <> 0 then c else
    	  (* let c = Pervasives.compare (X.nb_father s1) (X.nb_father s2) in *)
          (* if c <> 0 then c else *)
	  if Why3.Term.t_equal f1 f2 then 0
	  else Pervasives.compare f1 f2

module Q = Heap.Make (struct 
		       type t = f
		       let compare = compare_f
		     end )

module Set__Fset = struct type 'a set = Q.t end

(*------------------  End manually edited -------------------*)

type t =
  { mutable formula: unit; mutable elts: Fol__FOL.t Set__Fset.set }


let create (us: unit) : t = 
  (*-----------------  Begin manually edited ------------------*)
  { formula = ();
    elts = Q.empty }
  (*------------------  End manually edited -------------------*)

let push (f: Fol__FOL.t) (q: t) : unit =
  (*-----------------  Begin manually edited ------------------*)
  q.elts <- Q.add q.elts (List.rev (Translation.dnf_to_conj_list f))
  (*------------------  End manually edited -------------------*)

exception Empty

let is_empty (q: t) : bool =
  (*-----------------  Begin manually edited ------------------*)
  try ignore (Q.pop q.elts); false
  with Heap.EmptyHeap -> true
  (*------------------  End manually edited -------------------*)


let pop (q: t) : Fol__FOL.t =
  (*-----------------  Begin manually edited ------------------*)
  let r, elts = try Q.pop q.elts with Heap.EmptyHeap -> raise Empty in
  q.elts <- elts;
  r
  (*------------------  End manually edited -------------------*)


let clear (q: t) : unit =
  (*-----------------  Begin manually edited ------------------*)
  q.elts <- Q.empty
  (*------------------  End manually edited -------------------*)


let copy (q: t) : t =
  (*-----------------  Begin manually edited ------------------*)
  q
  (*------------------  End manually edited -------------------*)
