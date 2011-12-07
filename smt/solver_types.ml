
let ale = Hstring.make "<=" 
let alt = Hstring.make "<"
let agt = Hstring.make ">"

let is_le n = Hstring.compare n ale = 0
let is_lt n = Hstring.compare n alt = 0
let is_gt n = Hstring.compare n agt = 0


type var =
    {  vid : int;
       pa : atom;
       na : atom;
       mutable weight : float;
       mutable seen : bool;
       mutable level : int;
       mutable reason: reason}

and atom = 
    { var : var;
      lit : Literal.LT.t;
      neg : atom;
      mutable watched : clause Vec.t;
      mutable is_true : bool;
      aid : int }

and clause = 
    { name : string; 
      mutable atoms : atom Vec.t ; 
      mutable activity : float;
      mutable removed : bool;
      learnt : bool }

and reason = clause option

let dummy_lit = Literal.LT.make (Literal.Eq(Term.vrai,Term.vrai))

let rec dummy_var =
  { vid = -101;
    pa = dummy_atom;
    na = dummy_atom; 
    level = -1;
    reason = None;
    weight = -1.;
    seen = false}
and dummy_atom = 
  { var = dummy_var; 
    lit = dummy_lit;
    watched = {Vec.dummy=dummy_clause; data=[||]; sz=0};
    neg = dummy_atom;
    is_true = false;
    aid = -102 }
and dummy_clause = 
  { name = ""; 
    atoms = {Vec.dummy=dummy_atom; data=[||]; sz=0};
    activity = -1.;
    removed = false;
    learnt = false }


module MA = Literal.LT.Map
  
let ale = Hstring.make "<=" 
let alt = Hstring.make "<"
let agt = Hstring.make ">"
let is_le n = Hstring.compare n ale = 0
let is_lt n = Hstring.compare n alt = 0
let is_gt n = Hstring.compare n agt = 0

let normal_form lit =
  match Literal.LT.view lit with
    | Literal.Eq (t1,t2)  when Term.equal t2 Term.faux ->
      Literal.LT.make (Literal.Eq(t1,Term.vrai)), true

    | Literal.Eq (t1,t2)  when Term.equal t1 Term.faux ->
      Literal.LT.make (Literal.Eq(t2,Term.vrai)), true


    | Literal.Distinct(false, [t1;t2])  when Term.equal t1 Term.faux ->
      Literal.LT.make (Literal.Eq(t2,Term.vrai)), false

    | Literal.Distinct(false, [t1;t2])  when Term.equal t2 Term.faux ->
      Literal.LT.make (Literal.Eq(t1,Term.vrai)), false

    | Literal.Distinct(false, [t1;t2])  when Term.equal t1 Term.vrai ->
      Literal.LT.make (Literal.Eq(t2,Term.vrai)), true

    | Literal.Distinct(false, [t1;t2])  when Term.equal t2 Term.vrai ->
      Literal.LT.make (Literal.Eq(t1,Term.vrai)), true

    | Literal.Distinct(false,[_;_]) -> Literal.LT.neg lit, true

    | Literal.Builtin(true,n,[t1;t2]) when is_gt n ->
      Literal.LT.neg lit, true

    | Literal.Builtin(false,n,[t1;t2]) when is_le n ->
      Literal.LT.neg lit, true
    | _ -> lit, false


(* let normal_form lit = *)
(*   match Literal.LT.view lit with *)
(*     | Literal.Eq (t1,t2)  -> *)
(*         if Term.equal t2 Term.faux || Term.equal t1 Term.faux then *)
(*           Literal.LT.neg lit, true *)
(*         else *)
(*           lit, false *)

(*     | Literal.Distinct(false,[_;_]) -> Literal.LT.neg lit, true *)
(*     | Literal.Builtin(true,n,[t1;t2]) when Builtin.is_gt n -> *)
(*   Literal.LT.neg lit, true *)
    
(*     | Literal.Builtin(false,n,[t1;t2]) when Builtin.is_le n -> *)
(*   Literal.LT.neg lit, true *)
(*     | _ -> lit, false *)


let cpt_mk_var = ref 0
let ma = ref MA.empty
let make_var =
  fun lit ->
    let lit, negated = normal_form lit in
    try MA.find lit !ma, negated 
    with Not_found ->
      let cpt_fois_2 = !cpt_mk_var lsl 1 in
      let rec var  = 
	{ vid = !cpt_mk_var; 
	  pa = pa;
	  na = na; 
	  level = -1;
	  reason = None;
	  weight = 0.;
	  seen = false}
      and pa = 
	{ var = var; 
	  lit = lit;
	  watched = Vec.make 10 dummy_clause; 
	  neg = na;
	  is_true = false;
	  aid = cpt_fois_2 (* aid = vid*2 *) }
      and na = 
	{ var = var;
	  lit = Literal.LT.neg lit;
	  watched = Vec.make 10 dummy_clause;
	  neg = pa;
	  is_true = false;
	  aid = cpt_fois_2 + 1 (* aid = vid*2+1 *) } in 
      ma := MA.add lit var !ma;
      incr cpt_mk_var;
      var, negated

let made_vars_info () = !cpt_mk_var, MA.fold (fun lit var acc -> var::acc)!ma []

let add_atom lit =
  let var, negated = make_var lit in
  if negated then var.na else var.pa 

let make_clause name ali sz_ali is_learnt = 
  let atoms = Vec.from_list ali sz_ali dummy_atom in
  { name  = name;
    atoms = atoms;
    removed = false;
    learnt = is_learnt;
    activity = 0. }
    
let fresh_lname =
  let cpt = ref 0 in 
  fun () -> incr cpt; "L" ^ (string_of_int !cpt)

let fresh_dname =
  let cpt = ref 0 in 
  fun () -> incr cpt; "D" ^ (string_of_int !cpt)
    
let fresh_name =
  let cpt = ref 0 in 
  fun () -> incr cpt; "C" ^ (string_of_int !cpt)



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
  ma := MA.empty

(**************************************************
For later: compute tags for clauses or use dnets
***************************************************

let abstraction_of_clause atoms = 
  let atoms = Sort.sort atoms in
  let acc = ref (Gmp.Z.from_int 0) in
  for i = 0 to atoms.Vec.sz - 1 do
    
  done
  Array.iter
    (

    )
  assert false


open Gmp

let int i = Z.from_int i

let ( * ) i j = Z.mul i j
let ( + ) i j = Z.add i j
let ( / ) i j = Z.tdiv_q i j

let l1 = [int 0 ; int 2 ; int 5 ; int 7;  int 6]

let l2 = [int 2 ; int 555 ; int 7;  int 6]

let l3 = [int 2 ; int 1111555 ; int 7;  int 6]

let l4 = [int 1; int 10 ]

let l5 = [int 1; int 12; int 25; int 99; int 100; int 199 ]

let l6 = [int 11555]

let rec basis2 acc e =
  if e = int 0 then acc
  else basis2 (acc * (int 10)) (e / (int 10))

let basis l = List.fold_left (fun acc e -> max acc (basis2 (int 1) e)) (int 10) l

let convert_to_basis b l = 
  (*let b' = if b = int 10 then int 0 else b / (int 10) in*)
  let b' = b in
  List.map (fun e -> b' + e) l
  
let tag_of b l = 
  (*let b' = b / (int 10) in*)
  let res, _ = 
    List.fold_right
      (fun e (res,rang) ->
         let res = res + rang*e in
         Format.printf "> e=%a  et %a@." Z.print res;
         res, rang*b
      )l (int 0, int 1)
  in 
  Format.printf "-----@.res = %a@.------@." Z.print res;
  res


let b = basis l1
let l = convert_to_basis b l1
let _ = tag_of b l
let b = basis l2
let l = convert_to_basis b l2
let _ = tag_of b l
let b = basis l3
let l = convert_to_basis b l3
let _ = tag_of b l
let b = basis l4
let l = convert_to_basis b l4
let _ = tag_of b l
let b = basis l5
let l = convert_to_basis b l5
let _ = tag_of b l
let b = basis l6
let l = convert_to_basis b l6
let _ = tag_of b l

**********)

