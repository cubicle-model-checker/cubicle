(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2015                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Types
open Util
open Ast
open Format


type hstr_info = { hstr : Hstring.t ; hstr_i : info }

type var = hstr_info

type arr = { arr_n : hstr_info; arr_arg : var list }

type array = arr option

type term_info = Term.t * info 

type term =
  | TVar of var * info
  | TTerm of term_info * array 
     
type atom =
  | AVar of var * info
  | AAtom of Atom.t * info 
  | AEq of term * term * info 
  | ANeq of term * term * info 
  | ALe of term * term * info
  | ALt of term * term * info
    
type formula =
  | PAtom of atom 
  | PNot of info * formula * info
  | PAnd of formula list * info
  | POr of formula list * info 
  | PImp of formula * formula * info 
  | PEquiv of formula * formula * info 
  | PIte of formula * formula * formula * info
  | PForall of var list * formula * info  
  | PExists of var list * formula * info  
  | PForall_other of var list * formula * info 
  | PExists_other of var list * formula * info

type term_or_formula = PF of formula | PT of term

type cformula = formula

let function_defs = Hstring.H.create 17

type pup_psw = {pup_form : cformula ; pup_t : term ; pup_i : info}

type pswts  =  (pup_psw list * info)

type pglob_update = PUTerm of (term * info) | PUCase of (pswts)

type pup_arg = { arg_v : var list ; arg_i : info }

type pupdate = {
  pup_loc : info;
  pup_arr : hstr_info;
  pup_arg : var list * info;
  pup_swts : pswts ;
  pup_info : (Hstring.t * var list * term)  option;
}

type ptrans_pupdate = { t_pup_l : pupdate list ; t_pup_i : info}

type ptrans_req = { r_f : cformula ; r_i : info }

type ptrans_assign = { a_n : hstr_info  ; a_p : pglob_update ; a_i : info } 

type ptrans_nondet = { n_n : hstr_info  ; n_i : info}

type ptrans_s = { ptr_assigns : ptrans_assign list; ptr_upds : ptrans_pupdate ; 
                  ptr_nondets : ptrans_nondet list; ptr_i : info}

type ptransition = {
  ptr_name : hstr_info ;
  ptr_args : hstr_info list;
  ptr_reqs : ptrans_req ;
  ptr_s : ptrans_s;
  ptr_loc : info;
}

(* type unsafe = { i : info; vl : var list ; cf : cformula } *)



type ptr_type_constructors =  hstr_info * hstr_info list 
 
(* type smt_info = { smt : Smt.Type.t ; smt_i : info} *)

type psystem = {
  pglobals : (info * hstr_info * hstr_info) list;
  pconsts : (info * hstr_info * hstr_info) list;
  parrays : (info * hstr_info  * (hstr_info  list * hstr_info)) list;
  ptype_defs : (info * ptr_type_constructors) list;
  pinit : info *  hstr_info list * cformula;
  pinvs : (info * hstr_info list * cformula) list;
  punsafe : (info * hstr_info list * cformula) list;
  ptrans : ptransition list;
}


type pdecl =
  | PInit of (info * hstr_info list * cformula)
  | PInv of (info * hstr_info list * cformula)
  | PUnsafe of (info * hstr_info list * cformula)
  | PTrans of ptransition
  | PFun


let add_fun_def name args f =
  (* eprintf "add fun %a (%a)@." Hstring.print name Variable.print_vars args; *)
  Hstring.H.add function_defs name (args, f)


(* type subst = (Variable.t * term_or_formula) list *)


let restr_subst_to sigma vars =
  List.fold_left (fun acc -> function
      | v, PF (PAtom ((AVar (v', i)))) 
      | v, PT (TVar (v',i)) ->
        if Variable.Set.mem v vars then
          (v, v'.hstr)::acc
        else acc
      | v, PT (TTerm ((Elem(v', Var),i),_)) ->
         if Variable.Set.mem v vars then
          (v, v')::acc
        else acc
      | v,  _ ->
        if Variable.Set.mem v vars then
          failwith "Can only apply substitutions of kind var -> var \
                    inside terms and atom."
        else acc
    ) [] sigma

let subst_term sigma tt = match tt with
  | TVar (v,i) ->
    (match Hstring.list_assoc v.hstr sigma with
     | PT t -> t
     | PF _ -> failwith "Cannot apply formula substitution in term."
     | exception Not_found -> tt)
  | TTerm ((t,it),i) ->
    (* eprintf "susbst in term %a (%a)@." Term.print t *)
    (*   Variable.print_vars (Term.variables t |> Variable.Set.elements); *)
    let sigma' = restr_subst_to sigma (Term.variables t) in
    (* eprintf "subst in %a ::: %a@." print_term tt Variable.print_subst sigma'; *)
    let t' = Term.subst sigma' t in
    (* eprintf "   result %a@." Term.print t'; *)
    if t == t' then tt else TTerm ((t', it),i)

  
let subst_atom sigma aa = match aa with
  | AVar (v,i) ->
    (match Hstring.list_assoc v.hstr sigma with
     | PF f -> f
     | PT _ -> failwith "Cannot apply term substitution in atom."
     | exception Not_found -> PAtom (aa))
  | AEq (t1, t2, i) | ANeq (t1, t2, i) | ALe (t1, t2, i) | ALt (t1, t2, i) ->
    (* eprintf "susbst natom@."; *)
    let t1' = subst_term sigma t1 in
    let t2' = subst_term sigma t2 in
    if t1 == t1' && t2 == t2' then PAtom (aa)
    else
      PAtom (match aa with
          | AEq _ -> AEq (t1', t2', i)
          | ANeq _ -> ANeq (t1', t2', i)
          | ALe _ -> ALe (t1', t2', i)
          | ALt _ -> ALt (t1', t2', i)
          | _ -> assert false
      )
  | AAtom (a, i) ->
    let sigma' = restr_subst_to sigma (Atom.variables a) in
    let a' = Atom.subst sigma' a in
    if a == a' then PAtom (aa) else PAtom (AAtom (a', i))

let rec apply_subst sigma (f:formula) = match f with
  | PAtom (a) ->
    let f' = subst_atom sigma a in
    if f == f' then f else f'
  | PNot (not_i,nf,i) ->
    let nf' = apply_subst sigma nf in
    if nf == nf' then f else PNot (not_i, nf',i)
  | PAnd (l, i) ->
    let l' = List.map (apply_subst sigma ) l in
    if List.for_all2 (fun c c' -> c == c') l l' then f else PAnd (l', i)
  | POr (l, i) ->
    let l' = List.map (apply_subst sigma ) l in
    if List.for_all2 (fun c c' -> c == c') l l' then f else POr (l', i)
  | PImp (a, b, i) ->
    let a', b' = apply_subst sigma a, apply_subst sigma b in
    if a == a' && b == b' then f else PImp (a', b', i)
  | PIte (c, t, e, i) ->
    let c', t', e' =
      apply_subst sigma c, apply_subst sigma t, apply_subst sigma e in
    if c == c' && t == t' && e == e' then f else PIte (c', t', e', i)
  | PEquiv (a, b, i) ->
    let a', b' = apply_subst sigma a, apply_subst sigma b in
    if a == a' && b == b' then f else PEquiv (a', b', i)
  | PForall (vs, qf, i)
  | PExists (vs, qf, i)
  | PForall_other (vs, qf, i)
  | PExists_other (vs, qf, i) ->
    (* Removed shadowed variables *)
    let new_list = List.map (fun x -> x.hstr) vs in 
    let sigma = List.filter (fun (v,_) -> not (Hstring.list_mem v new_list)) sigma in
    let qf' = apply_subst sigma qf in
    if qf == qf' then f else match f with
      | PForall _ -> PForall (vs, qf', i)
      | PExists _ -> PExists (vs, qf', i)
      | PForall_other _ -> PForall_other (vs, qf', i)
      | PExists_other _ -> PExists_other (vs, qf', i)
      | _ -> assert false


let app_fun name args =
  try
    let vars, f = Hstring.H.find function_defs name in
    (* eprintf "app fun %a (%a)@." Hstring.print name Variable.print_vars vars; *)
    let nvars, nargs = List.length vars, List.length args in
    if nvars <> nargs then
      failwith (asprintf
                  "Wrong arity: %a takes %d arguments but was given %d."
                  Hstring.print name nvars nargs);
    let sigma = List.combine vars args in
    (* eprintf "app fun  subst : %a@." print_subst sigma; *)
    (* eprintf "app fun  in : %a@." print f; *)
    let r = apply_subst sigma f in
    (* eprintf "result : %a@." print r; *)
    r
  with Not_found ->
      failwith (asprintf "Undefined function symbol %a." Hstring.print name)



(* let neg_atom aa = match aa with *)
(*   | AVar v -> PNot (PAtom aa) *)
(*   | AAtom a -> PAtom (AAtom (Atom.neg a)) *)
(*   | AEq (t1, t2) -> PAtom (ANeq (t1, t2)) *)
(*   | ANeq (t1, t2) -> PAtom (AEq (t1, t2)) *)
(*   | ALe (t1, t2) -> PAtom (ALt(t2, t1)) *)
(*   | ALt (t1, t2) -> PAtom (ALe(t2, t1)) *)

(* let rec neg = function *)
(*   | PAtom a -> neg_atom a *)
(*   | PNot f -> f *)
(*   | PAnd l -> POr (List.map neg l) *)
(*   | POr l -> PAnd (List.map neg l) *)
(*   | PImp (a, b) -> PAnd [a; neg b] *)
(*   | PIte (c, t, e) -> POr [PAnd [c; neg t]; PAnd [neg c; e]] *)
(*   | PEquiv (a, b) -> POr [PAnd [a; neg b]; PAnd [neg a; b]] *)
(*   | PForall (vs, f) -> PExists (vs, neg f) *)
(*   | PExists (vs, f) -> PForall (vs, neg f) *)
(*   | PForall_other (vs, f) -> PExists_other (vs, neg f) *)
(*   | PExists_other (vs, f) -> PForall_other (vs, neg f) *)


(* let rec nnf = function *)
(*   | PAtom _ as a -> a *)
(*   | PNot f -> nnf (neg f) *)
(*   | PAnd l -> *)
(*     let l' = List.fold_left (fun acc x -> match nnf x with *)
(*         | PAnd xs -> List.rev_append xs acc *)
(*         | nx -> nx :: acc) [] l |> List.rev in *)
(*     PAnd l' *)
(*   | POr l -> *)
(*     let l' = List.fold_left (fun acc x -> match nnf x with *)
(*         | POr xs -> List.rev_append xs acc *)
(*         | nx -> nx :: acc) [] l |> List.rev in *)
(*     POr l' *)
(*   | PImp (a, b) -> nnf (POr [neg a; b]) *)
(*   | PIte (c, t, e) -> nnf (PAnd [POr [neg c; t]; POr [c; e]]) *)
(*   | PEquiv (a, b) -> nnf (PAnd [POr [neg a; b]; POr [a; neg b]]) *)
(*   | PForall (vs, f) -> PExists (vs, nnf f) *)
(*   | PExists (vs, f) -> PForall (vs, nnf f) *)
(*   | PForall_other (vs, f) -> PExists_other (vs, nnf f) *)
(*   | PExists_other (vs, f) -> PForall_other (vs, nnf f) *)


(* let list_of_conj = function  *)
(*   | PAnd l -> l *)
(*   | (\* PAtom _ as *\) a -> [a] *)

(* let list_of_disj = function  *)
(*   | POr l -> l *)
(*   | (\* PAtom _ as *\) a -> [a] *)

(* let list_of_cnf = function  *)
(*   | PAnd l -> l *)
(*   | (\* (PAtom _ | POr _) as *\) f -> [ f ] *)

(* let list_of_dnf = function  *)
(*   | POr l -> l *)
(*   | (\* (PAtom _ | PAnd _) as *\) f -> [ f ] *)

(* let cross a b = *)
(*   List.fold_left (fun acc la -> *)
(*       List.fold_left (fun acc' lb -> *)
(*           PAnd (list_of_conj lb @ list_of_conj la) :: acc' *)
(*         ) acc (list_of_dnf b) *)
(*     |> List.rev *)
(*     ) [] (list_of_dnf a) *)
(*   |> (fun l -> POr l) *)
    
(* let rec dnf_aux = function *)
(*   | PAtom _ | PNot _ as lit -> lit *)
(*   | PAnd (f :: l) -> *)
(*     List.fold_left (fun acc g -> *)
(*         cross (dnf_aux g) acc) *)
(*       (dnf_aux f) l *)
(*   | POr l -> *)
(*     let l' = List.fold_left (fun acc x -> match dnf_aux x with *)
(*         | POr xs -> List.rev_append xs acc *)
(*         | (\* (PAnd _ | PAtom _) as *\) nx -> nx :: acc) [] l |> List.rev in *)
(*     POr l' *)
(*   | PAnd [] -> assert false *)
(*   | PForall (vs, f) -> PExists (vs, dnf_aux f) *)
(*   | PExists (vs, f) -> PForall (vs, dnf_aux f) *)
(*   | PForall_other (vs, f) -> PExists_other (vs, dnf_aux f) *)
(*   | PExists_other (vs, f) -> PForall_other (vs, dnf_aux f) *)
(*   | _ -> assert false *)

(* let dnf f = dnf_aux (nnf f) *)


(* let fresh_var = *)
(*   let cpt = ref 0 in *)
(*   fun () -> *)
(*     incr cpt; *)
(*     Hstring.make ("_v"^string_of_int !cpt) *)


(* let rec foralls_above_and (vars, acc) = function *)
(*   | PForall (vs, f) :: l -> *)
(*     let sigma = List.map (fun v -> v, PT (TVar (fresh_var ()))) vs in *)
(*     let acc = apply_subst sigma f :: acc in *)
(*     let vars = List.rev_append vs vars in *)
(*     foralls_above_and (vars, acc) l *)
(*   | [] -> *)
(*     let c = PAnd (List.rev acc) in *)
(*     if vars = [] then c else PForall (List.rev vars, c) *)
(*   | f :: l -> *)
(*   (\* | (PEquiv _ | PImp _ | PIte _ | PNot _ | PVar _ | PAtom _ | PAnd _ | POr _ | PExists _ *\) *)
(*   (\*   | PForall_other _ | PExists_other _ as f) :: l -> *\) *)
(*     foralls_above_and (vars, f :: acc) l *)


(* let rec exists_above_or (vars, acc) = function *)
(*   | PExists (vs, f) :: l -> *)
(*     let sigma = List.map (fun v -> v, PT (TVar (fresh_var ()))) vs in *)
(*     let acc = apply_subst sigma f :: acc in *)
(*     let vars = List.rev_append vs vars in *)
(*     exists_above_or (vars, acc) l *)
(*   | [] -> *)
(*     let c = POr (List.rev acc) in *)
(*     if vars = [] then c else PExists (List.rev vars, c) *)
(*   (\* | ( PEquiv _ | PImp _ | PIte _ | PNot _ | PVar _ | PAtom _ | PAnd _ | POr _ | PForall _ *\) *)
(*   (\*   | PForall_other _ | PExists_other _ as f) :: l -> *\) *)
(*   | f :: l -> *)
(*         exists_above_or (vars, f :: acc) l *)


(* let rec up_quantifiers = function *)
(*   | PAtom _ as a -> a *)
(*   | PForall _ | PExists _ | PForall_other _ | PExists_other _  as f -> f *)
(*   | PAnd l -> *)
(*     let l' = List.map up_quantifiers l in *)
(*     foralls_above_and ([],[]) l' *)
(*   | POr l -> *)
(*     let l' = List.map up_quantifiers l in *)
(*     exists_above_or ([],[]) l' *)
(*   | PEquiv _ | PImp _ | PIte _ | PNot _  -> assert false *)


(* let conv_term = function *)
(*   | TVar v -> Elem (v, Var) *)
(*   | TTerm t -> t *)

(* let conv_atom aa = match aa with *)
(*   | AVar _ -> failwith "Remaining free variables in atom." *)
(*   | AEq (t1, t2) | ANeq (t1, t2) | ALe (t1, t2) | ALt (t1, t2) -> *)
(*     let t1 = conv_term t1 in *)
(*     let t2 = conv_term t2 in *)
(*     let op  = match aa with *)
(*        | AEq _ -> Eq *)
(*        | ANeq _ -> Neq *)
(*        | ALe _ -> Le *)
(*        | ALt _ -> Lt *)
(*        | _ -> assert false *)
(*     in *)
(*     Atom.Comp (t1, op, t2) *)
(*   | AAtom a -> a *)

(* let satom_of_atom_list = *)
(*   List.fold_left (fun acc -> function *)
(*       | PAtom a -> SAtom.add (conv_atom a) acc *)
(*       | x -> eprintf "%a@." print x;  assert false *)
(*     ) SAtom.empty *)
  
(* let satom_of_cube = function *)
(*   | PAtom a -> SAtom.singleton (conv_atom a) *)
(*   | PAnd l -> satom_of_atom_list l *)
(*   | _ -> assert false *)

(* let satoms_of_dnf = function *)
(*   | PAtom _ | PAnd _ as c -> [satom_of_cube c] *)
(*   | POr l -> List.map satom_of_cube l *)
(*   | _ -> assert false *)

(* let unsafes_of_formula f = *)
(*   match up_quantifiers (dnf f) with *)
(*   | PExists (vs, f) -> vs, satoms_of_dnf f *)
(*   | sf -> [], satoms_of_dnf sf *)

(* let inits_of_formula f = *)
(*   match up_quantifiers (dnf f) with *)
(*   | PForall (vs, f) -> vs, satoms_of_dnf f *)
(*   | sf -> [], satoms_of_dnf sf *)

(* let uguard_of_formula = function *)
(*   | PForall_other ([v], f) -> v, satoms_of_dnf f *)
(*   | _ -> assert false *)

(* let rec classify_guards (req, ureq) = function *)
(*   | [] -> PAnd req, ureq *)
(*   | PForall_other _ as f :: l -> classify_guards (req, f :: ureq) l *)
(*   | PAtom _ as f :: l -> classify_guards (f :: req, ureq) l *)
(*   | _ -> assert false *)

(* let rec guard_of_formula_aux = function *)
(*   | PAtom _ as f -> [satom_of_cube f, []] *)
(*   | PAnd l -> *)
(*     let req, ureq = classify_guards ([],[]) l in *)
(*     [satom_of_cube req, List.map uguard_of_formula ureq] *)
(*   | POr l -> List.map guard_of_formula_aux l |> List.flatten *)
(*   | _ -> assert false *)

(* let guard_of_formula f = *)
(*   match up_quantifiers (dnf f) with *)
(*   | PForall _ | PExists _ | PExists_other _ -> assert false *)
(*   | f -> guard_of_formula_aux f *)


(* (\* Encodings of Ptree systems to AST systems *\) *)

(* let encode_term = function *)
(*   | TVar v -> Elem (v, Var) *)
(*   | TTerm t -> t *)


(* let encode_pswts pswts = *)
(*   List.fold_left (fun acc (f, t) -> *)
(*       let d = satoms_of_dnf (dnf f) in *)
(*       let t = encode_term t in *)
(*       List.fold_left (fun acc sa -> (sa, t) :: acc) acc d *)
(*     ) [] pswts *)
(*   |> List.rev *)

(* let encode_pglob_update = function *)
(*   | PUTerm (t) -> UTerm (encode_term t) *)
(*   | PUCase (pswts) -> UCase (encode_pswts pswts)  *)


(* let encode_pinfo p =  *)
(*   match p with  *)
(*     |None -> None *)
(*     |Some (n,h,t) -> Some (n,h,encode_term t) *)

(* let encode_pupdate ({pup_loc; pup_arr; pup_arg; pup_swts; pup_info})= *)
(*   {  up_loc = pup_loc; *)
(*      up_arr = pup_arr; *)
(*      up_arg = pup_arg; *)
(*      up_swts = encode_pswts pup_swts; *)
(*      up_info = encode_pinfo pup_info; *)
(*   } *)

(* let encode_ptransition *)
(*     {ptr_name; ptr_args; ptr_reqs; ptr_assigns; *)
(*      ptr_upds; ptr_nondets; ptr_loc;} =    *)
(*   let dguards = guard_of_formula ptr_reqs.r_f in *)
(*   let tr_assigns = List.map (fun a -> *)
(*       { ta_n = a.a_n; ta_p = encode_pglob_update (a.a_p); ta_i = a.a_i}) ptr_assigns in *)
(*   let tr_nondets = List.map (fun a -> *)
(*       { tn_n = a.n_n ; tn_i = a.n_i}) ptr_nondets in *)
(*   let tr_upds = List.map encode_pupdate ptr_upds in *)
(*   List.rev_map (fun (req, ureq) -> *)
(*       {  tr_name = ptr_name; *)
(*          tr_args = ptr_args; *)
(*          tr_reqs = {tr_r = req; tr_info = ptr_reqs.r_i}; *)
(*          tr_ureq = ureq; *)
(*          tr_assigns; *)
(*          tr_upds; *)
(*          tr_nondets; *)
(*          tr_loc = ptr_loc } *)
(*     ) dguards *)



(* let encode_psystem *)
(*     {pglobals; pconsts; parrays; ptype_defs; *)
(*      pinit = init_loc, init_vars, init_f; *)
(*      pinvs; punsafe; ptrans} = *)
(*   let other_vars, init_dnf = inits_of_formula init_f in *)
(*   let init = init_loc, init_vars @ other_vars, init_dnf in *)
(*   let invs = *)
(*     List.fold_left (fun acc (inv_loc, inv_vars, inv_f) -> *)
(*         let other_vars, dnf = unsafes_of_formula inv_f in *)
(*         let inv_vars = inv_vars @ other_vars in *)
(*         List.fold_left (fun acc (sa) -> (inv_loc, inv_vars, sa) :: acc) acc dnf *)
(*       ) [] pinvs *)
(*     |> List.rev *)
(*   in *)
(*   let unsafe = *)
(*     List.fold_left (fun acc (unsafe_loc, unsafe_vars, unsafe_f) -> *)
(*         let other_vars, dnf = unsafes_of_formula unsafe_f in *)
(*         (\* List.iter (fun sa -> eprintf "unsafe : %a@." SAtom.print sa) dnf; *\) *)
(*         let unsafe_vars = unsafe_vars @ other_vars in *)
(*         List.fold_left *)
(*           (fun acc sa -> (unsafe_loc, unsafe_vars, sa) :: acc) acc dnf *)
(*       ) [] punsafe *)
(*   in *)
(*   let trans = *)
(*     List.fold_left (fun acc ptr -> *)
(*         List.fold_left (fun acc tr -> tr :: acc) acc (encode_ptransition ptr) *)
(*       ) [] ptrans *)
(*     |> List.sort (fun t1 t2  -> *)
(*         let c = compare (List.length t1.tr_args) (List.length t2.tr_args) in *)
(*         if c <> 0 then c else *)
(*         let c = compare (List.length t1.tr_upds) (List.length t2.tr_upds) in *)
(*         if c <> 0 then c else *)
(*         let c = compare (List.length t1.tr_ureq) (List.length t2.tr_ureq) in *)
(*         if c <> 0 then c else *)
(*         compare (SAtom.cardinal t1.tr_reqs.tr_r) (SAtom.cardinal t2.tr_reqs.tr_r) *)
(*       ) in *)
(*   { *)
(*     globals = pglobals; *)
(*     consts = pconsts; *)
(*     arrays = parrays; *)
(*     type_defs = ptype_defs; *)
(*     init; *)
(*     invs; *)
(*     unsafe; *)
(*     trans; *)
(*   } *)
      


let psystem_of_decls ~pglobals ~pconsts ~parrays ~ptype_defs pdecls =
  let inits, pinvs, punsafe, ptrans =
    List.fold_left (fun (inits, invs, unsafes, trans) -> function
        | PInit i -> i :: inits, invs, unsafes, trans
        | PInv i -> inits, i :: invs, unsafes, trans
        | PUnsafe u -> inits, invs, u :: unsafes, trans
        | PTrans t -> inits, invs, unsafes, t :: trans
        | PFun -> inits, invs, unsafes, trans
      ) ([],[],[],[]) pdecls
  in
  let pinit = match inits with
    | [i] -> i
    | [] -> failwith "No inititial formula."
    | _::_ -> failwith "Only one initital formula alowed."
  in
  { pglobals;
    pconsts;
    parrays;
    ptype_defs;
    pinit;
    pinvs;
    punsafe;
    ptrans }
  
  




(* (\* let rec formula_to_dnf = function *\) *)
(* (\*   | PAtom _ as pa -> pa *\) *)
(* (\*   | PNot f ->  *\) *)
(* (\*   | PAnd of formula * formula *\) *)
(* (\*   | POr of formula * formula *\) *)
(* (\*   | PImp of formula * formula *\) *)
(* (\*   | PIte of formula * formula * formula *\) *)
(* (\*   | PForall of Variable.t list * formula *\) *)
(* (\*   | PExists of Variable.t list * formula *\) *)
(* (\*   | PForall_other of Variable.t list * formula *\) *)
