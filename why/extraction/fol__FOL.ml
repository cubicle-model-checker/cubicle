(* This file has been generated from Why3 theory FOL *)
open Ast
open Global
open Format
module S = Set__Fset

type t = 
  | Lit of Atom.t
  | Not of t
  | Or of t list
  | And of t list
  | Forall of Hstring.t list * t
  | Exists of Hstring.t list * t

exception Compare of int
let rec compare f1 f2 = match f1, f2 with
  | Lit a1, Lit a2 -> Atom.compare a1 a2
  | Lit _, _ -> -1
  | _, Lit _ -> 1
  | Not x1, Not x2 -> compare x1 x2
  | Not _, _ -> -1
  | _, Not _ -> 1
  | And l1, And l2 | Or l1, Or l2 ->
    let r = Pervasives.compare (List.length l1) (List.length l2) in
    if r <> 0 then r
    else begin
      try 
	List.iter2 (fun x1 x2 ->
	  let r = compare x1 x2 in
	  if r <> 0 then raise (Compare r)
	) l1 l2;
	0	
      with Compare r -> r
    end
  | And _, _ -> -1
  | _, And _ -> 1
  | Or _, _ -> -1
  | _, Or _ -> 1
  | Forall (v1, f1), Forall (v2, f2) | Exists (v1, f1), Exists (v2, f2) ->
    let r = compare f1 f2 in
    if r <> 0 then r
    else
      let r = Pervasives.compare (List.length v1) (List.length v2) in
      if r <> 0 then r
      else begin
	  try 
	    List.iter2 (fun x1 x2 ->
			let r = Hstring.compare x1 x2 in
			if r <> 0 then raise (Compare r)
		       ) v1 v2;
	    0	
	  with Compare r -> r
	end
  | Forall _, _ -> -1
  | _, Forall _ -> 1


let rec print fmt = function
  | Lit a -> Pretty.print_atom fmt a 
  | Not f -> fprintf fmt "~%a" print f
  | Or l -> fprintf fmt "or(%a)" (print_list "\\/") l
  | And l -> fprintf fmt "and(%a)" (print_list "/\\") l
  | Forall (v, f) -> fprintf fmt "forall %a. %a" Pretty.print_args v print f
  | Exists (v, f) -> fprintf fmt "exists %a. %a" Pretty.print_args v print f

and print_list sep fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> fprintf fmt "%a %s %a" print x sep (print_list sep) r

(* type structure to be defined (uninterpreted type) *)

(* let infix_breq (x: structure) (x1: t) : bool = *)
(*   failwith "to be implemented" (\* uninterpreted symbol *\) *)

let ffalse  : t = Lit Atom.False

let ttrue  : t = Lit Atom.True


(*---------- Helper functions ----------------*)
let conj_to_cube_aux args l =
  if Options.debug then eprintf "c2ca: %a@." (print_list " , ") l;
  let sa = List.fold_left (fun acc f -> 
			   match f with 
			   | Lit x -> SAtom.add x acc
			   | _ -> assert false) SAtom.empty l in
  (* XXX: proper cube ? *)
  let arr_sa = ArrayAtom.of_satom sa in
  { !Global.global_system with 
    t_unsafe = args, sa;
    t_arru = arr_sa;
    t_alpha = ArrayAtom.alpha arr_sa args }

let conj_to_cube = function
  | Exists (args, And l) -> conj_to_cube_aux args l
  | Exists (args, Lit x) -> conj_to_cube_aux args [Lit x]
  | And l -> conj_to_cube_aux [] l
  | Lit x -> conj_to_cube_aux [] [Lit x]
  | _ -> assert false

let rec fol_to_cubes = function
  | Exists (_, And _) | Exists (_, Lit _) | Lit _ | And _ as f ->
						     if Options.debug then eprintf "f2c: %a @." print f;
						     [conj_to_cube f]
  | Or l as f -> List.fold_left (fun acc f -> fol_to_cubes f @ acc) [] l
  | _ -> assert false

let sa_to_f sa = And (SAtom.fold (fun x acc -> Lit x :: acc) sa [])

let cube_to_fol {t_unsafe = args, sa} = Exists (args, sa_to_f sa)

let cubes_to_fol = function
  | [] -> ffalse
  | [sa] -> cube_to_fol sa
  | lsa -> Or (List.map cube_to_fol lsa)


let init_to_fol {t_init = args, lsa} = match lsa with
  | [] -> ffalse
  | [sa] -> Forall (args, sa_to_f sa)
  | lsa -> Forall (args, Or (List.map sa_to_f lsa))

let init_to_fol ({t_init = args, lsa} as i) =
  let r = init_to_fol i in
  if Options.debug then
  (List.iter (fun sa -> eprintf "init: %a ===> @." Pretty.print_cube sa) lsa;
   eprintf "         ===> %a @." print r);
  r

(* let wrap_system sa = *)
(*   let sa, (args, _) = proper_cube sa in *)
(*   let arr_sa = ArrayAtom.of_satom sa in *)
(*   { global_system with  *)
(*     t_unsafe = args, sa; *)
(*     t_arru = arr_sa; *)
(*     t_alpha = ArrayAtom.alpha arr_sa args } *)
    

(* let fol_to_systems f = List.map wrap_system (fol_to_cubes f) *)

let rec push_neg p = function
  | Lit a as x -> if p then x else Lit (Atom.neg a)
  | Not f -> push_neg (not p) f
  | Or l ->
      if p then Or (List.map (push_neg p) l)
      else And (List.map (push_neg p) l)
  | And l ->
      if p then And (List.map (push_neg p) l)
      else Or (List.map (push_neg p) l)
  | Forall (v,f) ->
      if p then Forall (v, push_neg p f)
      else Exists (v, push_neg p f)
  | Exists (v,f) ->
      if p then Exists (v, push_neg p f)
      else Forall (v, push_neg p f)

let dnf f =
  let cons x xs = x :: xs in
  let rec fold g = function
    | And (_::_::_ as hs) -> List.fold_left fold g hs
    | Or (_::_::_ as hs) -> List.concat (List.map (fold g) hs)
    | And [h] | Or [h] | h -> List.map (cons h) g in
  fold [[]] (push_neg true f)

let reconstruct_dnf f =
  let l = List.map (function 
		       | [] -> ffalse
		       | [f] -> f
		       | conj -> And conj) (dnf f) in
  match l with
  | [] -> ffalse
  | [f'] -> f'
  | _ -> Or l
	       
let rec dnfize = function
  | Forall (v,f) -> Forall (v, dnfize f)
  | Exists (v,f) -> Exists (v, dnfize f)
  | f -> reconstruct_dnf f

(*-----------------------------------------------*)


let rec fol_apply_subst sigma = function
  | Lit a -> Lit (subst_atom sigma a)
  | Not f -> Not (fol_apply_subst sigma f)
  | Or l -> Or (List.map (fol_apply_subst sigma) l)
  | And l -> And (List.map (fol_apply_subst sigma) l)
  (* XXX: Alpha renaming ? *)
  | Forall (v,f) -> Forall (v, fol_apply_subst sigma f)
  | Exists (v,f) -> Exists (v, fol_apply_subst sigma f)


(*-----------------------------------------------*)




	
(* neg *)  
let prefix_tl (x: t) : t = dnfize (Not x)

let infix_et (x: t) (x1: t) : t = dnfize (And [x; x1])

let infix_plpl (x: t) (x1: t) : t = dnfize (Or [x; x1])

let infix_eqgt (x: t) (x1: t) : t = dnfize (Or [Not x; x1])
  
let infix_breqeq (x: t) (x1: t) : bool =
  if Options.debug then eprintf "do: %a  |=  %a@." print x print x1;
  let x, x1 = dnfize x, dnfize x1 in 
  let ls = fol_to_cubes x in
  match ls with
  | [s] -> Cube.fixpoint ~invariants:[] ~visited:(fol_to_cubes x1) s <> None
  | _ -> assert false


(* Notataions *)

let neg = prefix_tl

let (&) x x1 = infix_et x x1

let (++) x x1 = infix_plpl x x1

let (=>) x x1 = infix_eqgt x x1
  
let (|=) x x1 = infix_breqeq x x1

module HSet = Hstring.HSet

let rec collect_constants acc = function
  | Exists (vars, f) ->
     collect_constants 
       (List.fold_left (fun acc v -> HSet.add v acc) acc vars) f
  | Forall _ -> acc
  | And l | Or l -> List.fold_left collect_constants acc l
  | Not f -> collect_constants acc f
  | Lit _ -> acc (* XXX: Maybe it's already a constant *)


let rec contains_var v = function
  | Lit a -> has_var v a
  | Not f -> contains_var v f
  | And l | Or l -> List.exists (contains_var v) l
  | _ -> false


let rec remove_quantified vars = function
  | Lit a -> 
     if List.exists (fun v -> has_var v a) vars then ttrue else Lit a
  | Not f -> Not (remove_quantified vars f)
  | And l | Or l  as f-> 
	     let l' = List.filter (fun f -> 
			  not (List.exists (fun v -> contains_var v f) vars)) l
	     in
	     begin match f with And _ -> And l' | Or _ -> Or l' end
  | _ as f -> f

let rec inst_aux constants f = 
  match f with
  | Forall (vars, f) ->
     And (List.map (fun sigma ->
		    remove_quantified vars (fol_apply_subst sigma f))
		   (all_permutations vars constants))
  | Exists (_, f) -> (* XXX: Alpha renaming ? *)
     inst_aux constants f
  | And l -> And (List.map (inst_aux constants) l)
  | Or l -> Or (List.map (inst_aux constants) l)
  | Not f -> Not (inst_aux constants f)
  | Lit _ -> f
  (* dnfize ? *)

let instantiate_and_skolem f =
  let constants = HSet.elements (collect_constants HSet.empty f) in
  dnfize (inst_aux constants f)


(* let cnf_split_quantified f = *)
(*   match push_neg false f with *)
(*   | Lit _ as nf -> *)



let rec make_formula = function
  | Lit a -> Prover.make_literal a
  | And l -> Smt.Formula.make Smt.Formula.And (List.map make_formula l)
  | Or l -> Smt.Formula.make Smt.Formula.Or (List.map make_formula l)
  | _ -> assert false

module SMT = Prover.SMT

let distinct vars = 
  Smt.Formula.make_lit Smt.Formula.Neq 
		       (List.map (fun v -> Smt.Term.make_app v []) vars)

let sat (f: t) : bool =
  if Options.debug then eprintf "sat: %a@." print f;
  try
    SMT.clear ();
    if Options.debug then eprintf "is: %a, cs: %a@." print f Pretty.print_args
    (HSet.elements (collect_constants HSet.empty f));
    let f = instantiate_and_skolem f in
    if Options.debug then eprintf "is2: %a@." print f;
  
    SMT.assume 
      ~profiling:false ~id:0
      (distinct (HSet.elements (collect_constants HSet.empty f)));
    let f = make_formula f in
    SMT.assume ~profiling:false ~id:0 f;
    SMT.check  ~profiling:false ();
    true
  with Smt.Unsat _ -> false  


let valid (f: t) : bool = not (sat (prefix_tl f))
