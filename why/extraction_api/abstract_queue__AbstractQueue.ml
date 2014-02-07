(* This file has been generated from Why3 module AbstractQueue *)

type f = Fol__FOL.t

(*-----------------  Begin manually edited ------------------*)
(* let compare_f f1 f2 = *)
(*       let v1 = Fol__FOL.size f1 in *)
(*       let v2 = Fol__FOL.size f2 in *)
(*       let c = Pervasives.compare v1 v2 in *)
(*       if c <> 0 then c else *)
(*         let c1 = Fol__FOL.card f1 in *)
(*         let c2 = Fol__FOL.card f2 in *)
(*         let c = Pervasives.compare c1 c2 in *)
(*         if c <> 0 then c else *)
(*     	  (\* let c = Pervasives.compare (X.nb_father s1) (X.nb_father s2) in *\) *)
(*           (\* if c <> 0 then c else *\) *)
(* 	  if Why3.Term.t_equal f1 f2 then 0 *)
(* 	  else Pervasives.compare f1 f2 *)

(* module Q = Heap.Make (struct  *)
(* 		       type t = f *)
(* 		       let compare = compare_f *)
(* 		     end ) *)

(* module Set__Fset = struct type 'a set = Q.t end *)

module Set__Fset = Set__Fset.Make (Fol__FOL)
(*------------------  End manually edited -------------------*)

type t =
  { mutable formula: unit; mutable elts: Fol__FOL.t Set__Fset.set }


let create (us: unit) : t = 
  (*-----------------  Begin manually edited ------------------*)
  { formula = ();
    elts = Set__Fset.empty }
  (*------------------  End manually edited -------------------*)

let push (f: Fol__FOL.t) (q: t) : unit =
  (*-----------------  Begin manually edited ------------------*)
  let elts = List.fold_left
               (fun elts df -> Set__Fset.add df elts)
               q.elts (Translation.dnf_to_conj_list f) in
  q.elts <- elts
  (*------------------  End manually edited -------------------*)

exception Empty

let is_empty (q: t) : bool =
  (*-----------------  Begin manually edited ------------------*)
  Set__Fset.is_empty q.elts
  (*------------------  End manually edited -------------------*)


let pop (q: t) : Fol__FOL.t =
  (*-----------------  Begin manually edited ------------------*)
  try
    let r = Set__Fset.choose q.elts in
    q.elts <- Set__Fset.remove r q.elts;
    r
  with Not_found -> raise Empty
  (*------------------  End manually edited -------------------*)


let clear (q: t) : unit =
  (*-----------------  Begin manually edited ------------------*)
  q.elts <- Set__Fset.empty
  (*------------------  End manually edited -------------------*)


let copy (q: t) : t =
  (*-----------------  Begin manually edited ------------------*)
  { formula = (); elts = q.elts } 
  (*------------------  End manually edited -------------------*)
