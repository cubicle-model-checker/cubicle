(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
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

type ident =
    {
      iname : Hstring.t;
      mask : int;
      mutable ivalues : (atom * int) Vec.t;
      ivars : var Vec.t;
    }

and var =
    {  vid : int;
       ident : ident;
       pa : atom;
       na : atom;
       mutable weight : float;
       mutable seen : bool;
       mutable level : int;
       mutable reason: reason;
       mutable vpremise : premise}
      
and atom = 
    { aid : int;
      var : var;
      value : int;
      neg : atom;
      mutable is_true : bool;
      mutable watched : clause Vec.t;}

and clause = 
    { name : string; 
      mutable atoms : atom Vec.t ; 
      mutable activity : float;
      mutable removed : bool;
      learnt : bool;
      cpremise : premise }

and reason = clause option

and premise = clause list

let dummy_value = -1 (* ou min_int ou autre*)

let rec dummy_ident =
    { iname = Hstring.make "";
      mask = 2;
      ivalues = {Vec.dummy=dummy_atom, dummy_value; data=[||]; sz=0};
      ivars = {Vec.dummy=dummy_var; data=[||]; sz=0};
    }

and dummy_var =
  { vid = -101;
    ident = dummy_ident;
    pa = dummy_atom;
    na = dummy_atom;
    weight = -1.;
    seen = false;
    level = -1;
    reason = None;
    vpremise = []}

and dummy_atom = 
  { aid = -202;
    var = dummy_var;
    value = dummy_value;
    neg = dummy_atom;
    watched = {Vec.dummy=dummy_clause; data=[||]; sz=0};
    is_true = false;}

and dummy_clause = 
  { name = ""; 
    atoms = {Vec.dummy=dummy_atom; data=[||]; sz=0};
    activity = -1.;
    removed = false;
    learnt = false;
    cpremise = [] }


module Debug = struct
    
  let sign a = if a==a.var.pa then "" else "-"
      
  let level a =
    match a.var.level, a.var.reason with
      | n, _ when n < 0 -> assert false
      | 0, Some c -> sprintf "->0/%s" c.name
      | 0, None   -> "@0"
      | n, Some c -> sprintf "->%d/%s" n c.name
      | n, None   -> sprintf "@@%d" n

  let value a =
    if a.is_true then sprintf "[T%s]" (level a)
    else if a.neg.is_true then sprintf "[F%s]" (level a)
    else ""

  let value_ms_like a =
    if a.is_true then sprintf ":1%s" (level a)
    else if a.neg.is_true then sprintf ":0%s" (level a)
    else ":X"

  let premise fmt v =
    List.iter (fun {name=name} -> fprintf fmt "%s," name) v

  let atom fmt a =
    fprintf fmt "%s%d%s [%a = %d]"
      (sign a) (a.var.vid+1) (value a) Hstring.print a.var.ident.iname
      ((* (snd (Vec.last a.var.ident.ivalues)) land *) a.value)


  let atoms_list fmt l = List.iter (fprintf fmt "%a ; " atom) l
  let atoms_array fmt arr = Array.iter (fprintf fmt "%a ; " atom) arr

  let atoms_vec fmt vec =
    for i = 0 to Vec.size vec - 1 do
      fprintf fmt "%a ; " atom (Vec.get vec i)
    done

  let clause fmt {name=name; atoms=arr; cpremise=cp} =
    fprintf fmt "%s:{ %a}" name atoms_vec arr


end


module HA = Hashtbl.Make (struct
  type t = Hstring.t * int
  let equal (n1, v1) (n2, v2) = Hstring.equal n1 n2 && v1 = v2
  let hash (n, v) = Hstring.hash n * v
end)


module HI = Hstring.H

let cpt_mk_var = ref 0

let ha = HA.create 2001
let hi = HI.create 2001


let is_top a = a.var.ident.mask = a.value

let is_bottom a = a.value = 0

let fresh_lname =
  let cpt = ref 0 in 
  fun () -> incr cpt; "L" ^ (string_of_int !cpt)

let fresh_dname =
  let cpt = ref 0 in 
  fun () -> incr cpt; "D" ^ (string_of_int !cpt)
    
let fresh_ename =
  let cpt = ref 0 in 
  fun () -> incr cpt; "E" ^ (string_of_int !cpt)
    
let fresh_name =
  let cpt = ref 0 in 
  fun () -> incr cpt; "C" ^ (string_of_int !cpt)

let make_clause name ali sz_ali is_learnt premise = 
  let atoms = Vec.from_list ali sz_ali dummy_atom in
  { name  = name;
    atoms = atoms;
    removed = false;
    learnt = is_learnt;
    activity = 0.;
    cpremise = premise}
    

let mkident vname mask =
  try HI.find hi vname
  with Not_found ->
    let vec = Vec.make 10 (dummy_atom, dummy_value) in
    Vec.push vec (dummy_atom, mask);
    let i =
      { iname = vname;
        mask = mask;
        ivalues = vec;
        ivars = Vec.make 10 dummy_var;
      }
    in HI.add hi vname i;
    i


let make_bottom_clause l a j =
  let v = a.var.ident.ivalues in
  assert (Vec.size v > 1);
  let c = ref [a.neg] in
  for i = 1 to j do
    c := (fst (Vec.get v i)).neg :: !c
  done;
  let c = make_clause (fresh_ename ()) !c (j+1) true [] in
  (* printf "make_bottom -> %a@." Debug.clause c; *)
  l := (a.neg, c, (fst (Vec.last v)).var.level) :: !l;
  raise Exit
     
exception Found of (atom * clause * int)

let new_implied_facts l v = (* TODO : dichotomy *)
  let vals = v.ident.ivalues in
  let vpa = v.pa.value in
  let vna = v.na.value in
  try
    for i = 1 to Vec.size vals - 1 do
      let x = snd (Vec.get vals i) in
      if x land vpa = 0 then make_bottom_clause l v.pa i;
      if x land vna = 0 then make_bottom_clause l v.na i;
    done
  with Exit -> ()

let add_atom implied (vname, value, mask) =
    try HA.find ha (vname,value)
    with Not_found ->
      let cpt_fois_2 = !cpt_mk_var lsl 1 in
      let ident = mkident vname mask in
      let neg_value = ident.mask land (lnot value) in
      let rec var =
        { vid = !cpt_mk_var ;
          ident = ident;
          pa = pa;
          na = na;
          level = -1;
	  reason = None;
	  seen = false;
	  vpremise = [];
          weight = 0.;}
      and pa = 
	{ aid = cpt_fois_2;
          var = var;
          neg = na;
          value = value;
          is_true = false;
	  watched = Vec.make 10 dummy_clause;
	}
      and na =
	{ aid = cpt_fois_2 + 1;
          var = var;
          neg = pa;
          value = neg_value;
          is_true = false;
	  watched = Vec.make 10 dummy_clause;
        }
      in
      Vec.push ident.ivars var;
      if is_top pa then begin 
        pa.is_true <- true;
        pa.var.level <- 0;
      end;
      if is_bottom pa then begin 
        na.is_true <- true;
        na.var.level <- 0;
      end;
      HA.add ha (vname, value) pa;
      HA.add ha (vname, neg_value) na;
      incr cpt_mk_var;
      new_implied_facts implied var;
      pa
      

let made_vars_info () = !cpt_mk_var, HA.fold (fun _ a acc -> a :: acc) ha []



module Clause = struct
      
  let size c = Vec.size c.atoms
  let pop c = Vec.pop c.atoms
  let shrink c i = Vec.shrink  c.atoms i
  let last c = Vec.last c.atoms
  let get c i = Vec.get c.atoms i
  let set c i v = Vec.set c.atoms i v

end

let to_float i = float_of_int i

let to_int f = int_of_float f

let clear () =
  cpt_mk_var := 0;
  HA.clear ha;
  HI.clear hi

let same_ident a b = Hstring.equal a.var.ident.iname b.var.ident.iname
let is_bottom a =
  a.neg.is_true ||
  (snd (Vec.last a.var.ident.ivalues)) land a.value = 0


let check_bottom_clause a =
  let v = a.var.ident.ivalues in
  if not (is_bottom a) then None
  else begin
    assert (Vec.size v > 1);
    let size = ref 1 in
    let c = ref [a.neg] in
    (* eprintf "--check trail--@."; *)
    (* for i = 1 to Vec.size v - 1 do *)
    (*   eprintf "%a : %d@." Debug.atom (fst (Vec.get v i)) (snd (Vec.get v i)); *)
    (* done; *)
    (* eprintf "%a@." Debug.atom a; *)
    (* eprintf "---------------@."; *)

    for i = 1 to Vec.size v - 1 do
      let b = (fst (Vec.get v i)) in
      if b.var.level > 0 then begin
        c := b.neg :: !c;
        incr size
      end
    done;
    let cl = make_clause (fresh_ename ()) !c !size true [] in
    (* printf "check_bottom -> %a@." Debug.clause c; *)
    Some cl
  end


  let is_attached c =
    let w0 = (Vec.get c.atoms 0).neg.watched in
    let w1 = (Vec.get c.atoms 1).neg.watched in
    let f w = 
      try
        for i = 0 to Vec.size w - 1 do
          if Vec.get w i == c  then raise Exit
        done;
        false
      with Exit -> true
    in
    f w0 && f w1


let enqueue_ident a =
  let values = a.var.ident.ivalues in
  Vec.push values (a, ((snd (Vec.last values)) land a.value));
  let l = ref [] in
  let ivars = a.var.ident.ivars in
  let lvl = a.var.level in
  for i = 0 to Vec.size ivars - 1 do
    let v = Vec.get ivars i in
    if v.level < 0 then
    match check_bottom_clause v.pa with
      | Some c ->
          l := (v.na, c, lvl) :: !l
      | None -> 
          match check_bottom_clause v.na
          with
            | Some c ->
                l := (v.pa, c, lvl) :: !l
            | None -> ()
  done;
  !l

let pop_ident a = Vec.pop a.var.ident.ivalues;
  assert (Vec.size a.var.ident.ivalues > 0)

