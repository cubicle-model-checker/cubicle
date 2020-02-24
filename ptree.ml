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



type term =
  | TVar of Variable.t
  | TTerm of Term.t
    
type atom =
  | AVar of Variable.t
  | AAtom of Atom.t
  | AEq of term * term
  | ANeq of term * term
  | ALe of term * term
  | ALt of term * term

type formula =
  | PAtom of atom
  | PNot of formula
  | PAnd of formula list
  | POr of formula list
  | PImp of formula * formula
  | PEquiv of formula * formula
  | PIte of formula * formula * formula
  | PForall of Variable.t list * formula
  | PExists of Variable.t list * formula
  | PForall_other of Variable.t list * formula
  | PExists_other of Variable.t list * formula


type term_or_formula = PF of formula | PT of term

type cformula = formula


let function_defs = Hstring.H.create 17


(* type cformula = [ *)
(*   | PAtom of Atom.t *)
(*   | PNot of cformula *)
(*   | PAnd of cformula list *)
(*   | POr of cformula list *)
(*   | PImp of cformula * cformula *)
(*   | PEquiv of cformula * cformula *)
(*   | PIte of cformula * cformula * cformula *)
(*   | PForall of Variable.t list * cformula *)
(*   | PExists of Variable.t list * cformula *)
(*   | PForall_other of Variable.t list * cformula *)
(*   | PExists_other of Variable.t list * cformula *)
(* ] *)

let print_term fmt = function
  | TVar v -> fprintf fmt "'%a" Hstring.print v
  | TTerm t -> Term.print fmt t

let print_atom fmt = function
  | AVar v -> fprintf fmt "?%a" Hstring.print v
  | AAtom a -> Atom.print fmt a
  | AEq (t1, t2) -> fprintf fmt "(= %a %a)" print_term t1 print_term t2
  | ANeq (t1, t2) -> fprintf fmt "(<> %a %a)" print_term t1 print_term t2
  | ALe (t1, t2) -> fprintf fmt "(<= %a %a)" print_term t1 print_term t2
  | ALt (t1, t2) -> fprintf fmt "(< %a %a)" print_term t1 print_term t2

let rec print fmt = function
  | PAtom a -> print_atom fmt a
  | PNot f -> fprintf fmt "~ %a" print f
  | PAnd l ->
    fprintf fmt "(and";
    List.iter (fprintf fmt " %a" print) l;
    fprintf fmt ")";
  | POr l ->
    fprintf fmt "(or";
    List.iter (fprintf fmt " %a" print) l;
    fprintf fmt ")";
  | PImp (a, b) -> fprintf fmt "(%a => %a)" print a print b
  | PEquiv (a, b) -> fprintf fmt "(%a <=> %a)" print a print b
  | PIte (c, t, e) ->
    fprintf fmt "(if %a then %a else %a)" print c print t print e
  | PForall (vs, f) ->
    fprintf fmt "(forall";
    List.iter (fprintf fmt " %a" Variable.print) vs;
    fprintf fmt ". %a)" print f
  | PExists (vs, f) ->
    fprintf fmt "(exists";
    List.iter (fprintf fmt " %a" Variable.print) vs;
    fprintf fmt ". %a)" print f
  | PForall_other (vs, f) ->
    fprintf fmt "(forall_other";
    List.iter (fprintf fmt " %a" Variable.print) vs;
    fprintf fmt ". %a)" print f
  | PExists_other (vs, f) ->
    fprintf fmt "(exists_other";
    List.iter (fprintf fmt " %a" Variable.print) vs;
    fprintf fmt ". %a)" print f


let print_tof fmt = function
  | PF f -> fprintf fmt "F<%a>" print f
  | PT t -> fprintf fmt "T<%a>" print_term t

let print_subst fmt =
  List.iter (fun (v, tof) ->
      fprintf fmt " %a -> %a, " Hstring.print v print_tof tof
    )


(* type atom = [ PAtom of Atom.t ] *)

(* type clause = [atom | POr of atom list] *)

(* type conj = [atom | PAnd of atom list] *)

(* type cnf = [clause | PAnd of clause list] *)

(* type dnf = [conj | POr of conj list] *)

(* type uguard = [PForall_other of Variable.t list * dnf] *)

(* type guard = [dnf | uguard] *)

(* type prenex_forall_dnf = [dnf | PForall of Variable.t list * dnf] *)

(* type cube = [conj | PExists of Variable.t list * conj] *)


type pswts = (cformula * term) list

type precord = Hstring.t * (Hstring.t * term)
type withrec = Hstring.t * (Hstring.t * term) list

type pglob_update = PUTerm of term | PUCase of pswts | PURecord of precord | PUWithRec of withrec 

type pupdate = {
  pup_loc : loc;
  pup_arr : Hstring.t;
  pup_arr_field : Hstring.t option;
  pup_arg : Variable.t list;
  pup_swts : pswts;
}

type ptransition = {
  ptr_lets : (Hstring.t * term) list;
  ptr_name : Hstring.t;
  ptr_args : Variable.t list;
  ptr_reqs : cformula;
  ptr_assigns : (Hstring.t * pglob_update) list;
  ptr_upds : pupdate list;
  ptr_nondets : Hstring.t list;
  ptr_loc : loc;
}

type psystem = {
  pglobals : (loc * Hstring.t * Smt.Type.t) list;
  pconsts : (loc * Hstring.t * Smt.Type.t) list;
  parrays : (loc * Hstring.t * (Smt.Type.t list * Smt.Type.t)) list;
  (*ptype_defs : (loc * Ast.type_constructors) list;*)
  ptype_defs : Ast.type_defs list;
  pinit : loc * Variable.t list * cformula;
  pinvs : (loc * Variable.t list * cformula) list;
  punsafe : (loc * Variable.t list * cformula) list;
  ptrans : ptransition list;
}


type pdecl =
  | PInit of (loc * Variable.t list * cformula)
  | PInv of (loc * Variable.t list * cformula)
  | PUnsafe of (loc * Variable.t list * cformula)
  | PTrans of ptransition
  | PFun


let add_fun_def name args f =
  (* eprintf "add fun %a (%a)@." Hstring.print name Variable.print_vars args; *)
  Hstring.H.add function_defs name (args, f)


type subst = (Variable.t * term_or_formula) list


let restr_subst_to sigma vars =
  List.fold_left (fun acc -> function
      | v, PF (PAtom (AVar v'))
      | v, PT (TVar v')
      | v, PT (TTerm (Elem(v', Var))) ->
        if Variable.Set.mem v vars then
          (v, v') :: acc
        else acc
      | v,  _ ->
        if Variable.Set.mem v vars then
          failwith "Can only apply substitutions of kind var -> var \
                    inside terms and atom."
        else acc
    ) [] sigma

let subst_term sigma tt = match tt with
  | TVar v ->
    (match Hstring.list_assoc v sigma with
     | PT t -> t
     | PF _ -> failwith "Cannot apply formula substitution in term."
     | exception Not_found -> tt)
  | TTerm t ->
    (* eprintf "susbst in term %a (%a)@." Term.print t *)
    (*   Variable.print_vars (Term.variables t |> Variable.Set.elements); *)
    let sigma' = restr_subst_to sigma (Term.variables t) in
    (* eprintf "subst in %a ::: %a@." print_term tt Variable.print_subst sigma'; *)
    let t' = Term.subst sigma' t in
    (* eprintf "   result %a@." Term.print t'; *)
    if t == t' then tt else TTerm t'

let subst_atom sigma aa = match aa with
  | AVar v ->
    (match Hstring.list_assoc v sigma with
     | PF f -> f
     | PT _ -> failwith "Cannot apply term substitution in atom."
     | exception Not_found -> PAtom aa)
  | AEq (t1, t2) | ANeq (t1, t2) | ALe (t1, t2) | ALt (t1, t2) ->
    (* eprintf "susbst natom@."; *)
    let t1' = subst_term sigma t1 in
    let t2' = subst_term sigma t2 in
    if t1 == t1' && t2 == t2' then PAtom aa
    else
      PAtom (match aa with
          | AEq _ -> AEq (t1', t2')
          | ANeq _ -> ANeq (t1', t2')
          | ALe _ -> ALe (t1', t2')
          | ALt _ -> ALt (t1', t2')
          | _ -> assert false
        )
  | AAtom a ->
    let sigma' = restr_subst_to sigma (Atom.variables a) in
    let a' = Atom.subst sigma' a in
    if a == a' then PAtom aa else PAtom (AAtom a')

let rec apply_subst sigma (f:formula) = match f with
  | PAtom a ->
    let f' = subst_atom sigma a in
    if f == f' then f else f'
  | PNot nf ->
    let nf' = apply_subst sigma nf in
    if nf == nf' then f else PNot nf'
  | PAnd l ->
    let l' = List.map (apply_subst sigma) l in
    if List.for_all2 (fun c c' -> c == c') l l' then f else PAnd l'  
  | POr l ->
    let l' = List.map (apply_subst sigma) l in
    if List.for_all2 (fun c c' -> c == c') l l' then f else POr l'  
  | PImp (a, b) ->
    let a', b' = apply_subst sigma a, apply_subst sigma b in
    if a == a' && b == b' then f else PImp (a', b')
  | PIte (c, t, e) ->
    let c', t', e' =
      apply_subst sigma c, apply_subst sigma t, apply_subst sigma e in
    if c == c' && t == t' && e == e' then f else PIte (c', t', e')
  | PEquiv (a, b) ->
    let a', b' = apply_subst sigma a, apply_subst sigma b in
    if a == a' && b == b' then f else PEquiv (a', b')
  | PForall (vs, qf)
  | PExists (vs, qf)
  | PForall_other (vs, qf)
  | PExists_other (vs, qf) ->
    (* Removed shadowed variables *)
    let sigma = List.filter (fun (v,_) -> not (Hstring.list_mem v vs)) sigma in
    let qf' = apply_subst sigma qf in
    if qf == qf' then f else match f with
      | PForall _ -> PForall (vs, qf')
      | PExists _ -> PExists (vs, qf')
      | PForall_other _ -> PForall_other (vs, qf')
      | PExists_other _ -> PExists_other (vs, qf')
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



let neg_atom aa = match aa with
  | AVar v -> PNot (PAtom aa)
  | AAtom a -> PAtom (AAtom (Atom.neg a))
  | AEq (t1, t2) -> PAtom (ANeq (t1, t2))
  | ANeq (t1, t2) -> PAtom (AEq (t1, t2))
  | ALe (t1, t2) -> PAtom (ALt(t2, t1))
  | ALt (t1, t2) -> PAtom (ALe(t2, t1))

let rec neg = function
  | PAtom a -> neg_atom a
  | PNot f -> f
  | PAnd l -> POr (List.map neg l)
  | POr l -> PAnd (List.map neg l)
  | PImp (a, b) -> PAnd [a; neg b]
  | PIte (c, t, e) -> POr [PAnd [c; neg t]; PAnd [neg c; e]]
  | PEquiv (a, b) -> POr [PAnd [a; neg b]; PAnd [neg a; b]]
  | PForall (vs, f) -> PExists (vs, neg f)
  | PExists (vs, f) -> PForall (vs, neg f)
  | PForall_other (vs, f) -> PExists_other (vs, neg f)
  | PExists_other (vs, f) -> PForall_other (vs, neg f)


let rec nnf = function
  | PAtom _ as a -> a
  | PNot f -> nnf (neg f)
  | PAnd l ->
    let l' = List.fold_left (fun acc x -> match nnf x with
        | PAnd xs -> List.rev_append xs acc
        | nx -> nx :: acc) [] l |> List.rev in
    PAnd l'
  | POr l ->
    let l' = List.fold_left (fun acc x -> match nnf x with
        | POr xs -> List.rev_append xs acc
        | nx -> nx :: acc) [] l |> List.rev in
    POr l'
  | PImp (a, b) -> nnf (POr [neg a; b])
  | PIte (c, t, e) -> nnf (PAnd [POr [neg c; t]; POr [c; e]])
  | PEquiv (a, b) -> nnf (PAnd [POr [neg a; b]; POr [a; neg b]])
  | PForall (vs, f) -> PExists (vs, nnf f)
  | PExists (vs, f) -> PForall (vs, nnf f)
  | PForall_other (vs, f) -> PExists_other (vs, nnf f)
  | PExists_other (vs, f) -> PForall_other (vs, nnf f)


let list_of_conj = function 
  | PAnd l -> l
  | (* PAtom _ as *) a -> [a]

let list_of_disj = function 
  | POr l -> l
  | (* PAtom _ as *) a -> [a]

let list_of_cnf = function 
  | PAnd l -> l
  | (* (PAtom _ | POr _) as *) f -> [ f ]

let list_of_dnf = function 
  | POr l -> l
  | (* (PAtom _ | PAnd _) as *) f -> [ f ]

let cross a b =
  List.fold_left (fun acc la ->
      List.fold_left (fun acc' lb ->
          PAnd (list_of_conj lb @ list_of_conj la) :: acc'
        ) acc (list_of_dnf b)
    |> List.rev
    ) [] (list_of_dnf a)
  |> (fun l -> POr l)
    
let rec dnf_aux = function
  | PAtom _ | PNot _ as lit -> lit
  | PAnd (f :: l) ->
    List.fold_left (fun acc g ->
        cross (dnf_aux g) acc)
      (dnf_aux f) l
  | POr l ->
    let l' = List.fold_left (fun acc x -> match dnf_aux x with
        | POr xs -> List.rev_append xs acc
        | (* (PAnd _ | PAtom _) as *) nx -> nx :: acc) [] l |> List.rev in
    POr l'
  | PAnd [] -> assert false
  | PForall (vs, f) -> PExists (vs, dnf_aux f)
  | PExists (vs, f) -> PForall (vs, dnf_aux f)
  | PForall_other (vs, f) -> PExists_other (vs, dnf_aux f)
  | PExists_other (vs, f) -> PForall_other (vs, dnf_aux f)
  | _ -> assert false

let dnf f = dnf_aux (nnf f)


let fresh_var =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    Hstring.make ("_v"^string_of_int !cpt)


let rec foralls_above_and (vars, acc) = function
  | PForall (vs, f) :: l ->
    let sigma = List.map (fun v -> v, PT (TVar (fresh_var ()))) vs in
    let acc = apply_subst sigma f :: acc in
    let vars = List.rev_append vs vars in
    foralls_above_and (vars, acc) l
  | [] ->
    let c = PAnd (List.rev acc) in
    if vars = [] then c else PForall (List.rev vars, c)
  | f :: l ->
  (* | (PEquiv _ | PImp _ | PIte _ | PNot _ | PVar _ | PAtom _ | PAnd _ | POr _ | PExists _ *)
  (*   | PForall_other _ | PExists_other _ as f) :: l -> *)
    foralls_above_and (vars, f :: acc) l


let rec exists_above_or (vars, acc) = function
  | PExists (vs, f) :: l ->
    let sigma = List.map (fun v -> v, PT (TVar (fresh_var ()))) vs in
    let acc = apply_subst sigma f :: acc in
    let vars = List.rev_append vs vars in
    exists_above_or (vars, acc) l
  | [] ->
    let c = POr (List.rev acc) in
    if vars = [] then c else PExists (List.rev vars, c)
  (* | ( PEquiv _ | PImp _ | PIte _ | PNot _ | PVar _ | PAtom _ | PAnd _ | POr _ | PForall _ *)
  (*   | PForall_other _ | PExists_other _ as f) :: l -> *)
  | f :: l ->
        exists_above_or (vars, f :: acc) l


let rec up_quantifiers = function
  | PAtom _ as a -> a
  | PForall _ | PExists _ | PForall_other _ | PExists_other _  as f -> f
  | PAnd l ->
    let l' = List.map up_quantifiers l in
    foralls_above_and ([],[]) l'
  | POr l ->
    let l' = List.map up_quantifiers l in
    exists_above_or ([],[]) l'
  | PEquiv _ | PImp _ | PIte _ | PNot _  -> assert false


let conv_term = function
  | TVar v -> Elem (v, Var)
  | TTerm t -> t

let conv_atom aa = match aa with
  | AVar _ -> failwith "Remaining free variables in atom."
  | AEq (t1, t2) | ANeq (t1, t2) | ALe (t1, t2) | ALt (t1, t2) ->
    let t1 = conv_term t1 in
    let t2 = conv_term t2 in
    let op  = match aa with
       | AEq _ -> Eq
       | ANeq _ -> Neq
       | ALe _ -> Le
       | ALt _ -> Lt
       | _ -> assert false
    in
    Atom.Comp (t1, op, t2)
  | AAtom a -> a

let satom_of_atom_list =
  List.fold_left (fun acc -> function
      | PAtom a -> SAtom.add (conv_atom a) acc
      | x -> eprintf "%a@." print x;  assert false
    ) SAtom.empty
  
let satom_of_cube = function
  | PAtom a -> SAtom.singleton (conv_atom a)
  | PAnd l -> satom_of_atom_list l
  | _ -> assert false

let satoms_of_dnf = function
  | PAtom _ | PAnd _ as c -> [satom_of_cube c]
  | POr l -> List.map satom_of_cube l
  | _ -> assert false

let unsafes_of_formula f =
  match up_quantifiers (dnf f) with
  | PExists (vs, f) -> vs, satoms_of_dnf f
  | sf -> [], satoms_of_dnf sf

let inits_of_formula f =
  match up_quantifiers (dnf f) with
  | PForall (vs, f) -> vs, satoms_of_dnf f
  | sf -> [], satoms_of_dnf sf

let rec forall_to_others tr_args f = match f with
  | PAtom _ -> f
  | PNot f1 ->
    let f1' = forall_to_others tr_args f1 in
    if f1 == f1' then f else PNot f1'
  | PAnd l ->
    let l' = List.map (forall_to_others tr_args) l in
    if List.for_all2 (==) l l' then f else PAnd l'
  | POr l ->
    let l' = List.map (forall_to_others tr_args) l in
    if List.for_all2 (==) l l' then f else POr l'
  | PImp (a, b) ->
    let a' = forall_to_others tr_args a in
    let b' = forall_to_others tr_args b in
    if a == a' && b == b' then f else PImp(a', b')
  | PIte (c, t, e) ->
    let c' = forall_to_others tr_args c in
    let t' = forall_to_others tr_args t in
    let e' = forall_to_others tr_args e in
    if c == c' && t == t' && e == e' then f else PIte(c', t', e')
  | PEquiv (a, b) ->
    let a' = forall_to_others tr_args a in
    let b' = forall_to_others tr_args b in
    if a == a' && b == b' then f else PEquiv(a', b')
  | PForall ([v], f) ->
    PAnd (PForall_other ([v], f) ::
          List.map (fun a -> apply_subst [v, PT (TVar a)] f) tr_args)
  | PForall  _ | PExists _ | PForall_other _ | PExists_other _ -> f
 

let uguard_of_formula = function
  | PForall_other ([v], f) -> v, satoms_of_dnf f
  | _ -> assert false

let rec classify_guards (req, ureq) = function
  | [] -> PAnd req, ureq
  | PForall_other _ as f :: l -> classify_guards (req, f :: ureq) l
  | PAtom _ as f :: l -> classify_guards (f :: req, ureq) l
  | _ -> assert false

let rec guard_of_formula_aux = function
  | PAtom _ as f -> [satom_of_cube f, []]
  | PAnd l ->
    let req, ureq = classify_guards ([],[]) l in
    [satom_of_cube req, List.map uguard_of_formula ureq]
  | POr l -> List.map guard_of_formula_aux l |> List.flatten
  | f ->
    let req, ureq = classify_guards ([],[]) [f] in
    [satom_of_cube req, List.map uguard_of_formula ureq]
  (* | _ -> assert false *)

let guard_of_formula tr_args f =
  match f |> forall_to_others tr_args |> dnf |> up_quantifiers with
  | PForall _ | PExists _ | PExists_other _ -> assert false
  | f -> guard_of_formula_aux f


(* Encodings of Ptree systems to AST systems *)

let encode_term = function
  | TVar v -> Elem (v, Var)
  | TTerm t -> t


let encode_pswts pswts =
  List.fold_left (fun acc (f, t) ->
      let d = satoms_of_dnf (dnf f) in
      let t = encode_term t in
      List.fold_left (fun acc sa -> (sa, t) :: acc) acc d
    ) [] pswts
  |> List.rev

let encode_pglob_update = function
  | PUTerm t -> UTerm (encode_term t)
  | PUCase pswts -> UCase (encode_pswts pswts)
  | PURecord (n, (f, v)) -> URecord (RecField (n, (f, encode_term v)))
  | PUWithRec (n, l) -> URecord (RecWith (n, List.map (fun (n,e) -> (n, encode_term e)) l   )) 

let encode_pupdate {pup_loc; pup_arr; pup_arr_field; pup_arg; pup_swts} =
  {  up_loc = pup_loc;
     up_arr = pup_arr;
     up_arr_field = pup_arr_field;
     up_arg = pup_arg;
     up_swts = encode_pswts pup_swts;
  }

let encode_ptransition
    {ptr_lets; ptr_name; ptr_args; ptr_reqs; ptr_assigns;
     ptr_upds; ptr_nondets; ptr_loc;} =
  let dguards = guard_of_formula ptr_args ptr_reqs in
  let tr_assigns = List.map (fun (i, pgu) ->
      (i, encode_pglob_update pgu)) ptr_assigns in
  let tr_upds = List.map encode_pupdate ptr_upds in
  let tr_lets = List.map (fun (x, t) -> (x, encode_term t)) ptr_lets in
  List.rev_map (fun (req, ureq) ->
      {  tr_name = ptr_name;
         tr_args = ptr_args;
         tr_reqs = req;
         tr_ureq = ureq;
	 tr_lets = tr_lets;
         tr_assigns;
         tr_upds;
         tr_nondets = ptr_nondets;
         tr_loc = ptr_loc }
    ) dguards


let encode_psystem
    {pglobals; pconsts; parrays; ptype_defs;
     pinit = init_loc, init_vars, init_f;
     pinvs; punsafe; ptrans} =
  let other_vars, init_dnf = inits_of_formula init_f in
  let init = init_loc, init_vars @ other_vars, init_dnf in
  let invs =
    List.fold_left (fun acc (inv_loc, inv_vars, inv_f) ->
        let other_vars, dnf = unsafes_of_formula inv_f in
        let inv_vars = inv_vars @ other_vars in
        List.fold_left (fun acc sa -> (inv_loc, inv_vars, sa) :: acc) acc dnf
      ) [] pinvs
    |> List.rev
  in
  let unsafe =
    List.fold_left (fun acc (unsafe_loc, unsafe_vars, unsafe_f) ->
        let other_vars, dnf = unsafes_of_formula unsafe_f in
        (* List.iter (fun sa -> eprintf "unsafe : %a@." SAtom.print sa) dnf; *)
        let unsafe_vars = unsafe_vars @ other_vars in
        List.fold_left
          (fun acc sa -> (unsafe_loc, unsafe_vars, sa) :: acc) acc dnf
      ) [] punsafe
  in
  let trans =
    List.fold_left (fun acc ptr ->
        List.fold_left (fun acc tr -> tr :: acc) acc (encode_ptransition ptr)
      ) [] ptrans
    |> List.sort (fun t1 t2  ->
        let c = compare (List.length t1.tr_args) (List.length t2.tr_args) in
        if c <> 0 then c else
        let c = compare (List.length t1.tr_upds) (List.length t2.tr_upds) in
        if c <> 0 then c else
        let c = compare (List.length t1.tr_ureq) (List.length t2.tr_ureq) in
        if c <> 0 then c else
        compare (SAtom.cardinal t1.tr_reqs) (SAtom.cardinal t2.tr_reqs)
      )
  in
  {
    globals = pglobals;
    consts = pconsts;
    arrays = parrays;
    type_defs = ptype_defs;
    init;
    invs;
    unsafe;
    trans;
  }
      


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
  
  

let print_type_defs fmt =
  List.iter (function
      | _, (ty, []) ->
        fprintf fmt "@{<fg_magenta>type@} @{<fg_green>%a@}" Hstring.print ty
      | _, (ty, cstrs) ->
        fprintf fmt "@{<fg_magenta>type@} @{<fg_green>%a@} = @[<hov>%a@]\n"
          Hstring.print ty
          (Pretty.print_list
             (fun fmt -> fprintf fmt "@{<fg_blue>%a@}" Hstring.print)
             "@ | ") cstrs
    )

let print_globals fmt  =
  List.iter (fun (_, g, ty) ->
      fprintf fmt "@{<fg_magenta>var@} @{<fg_red>%a@} : @{<fg_green>%a@}@."
        Hstring.print g Hstring.print ty
    )
     
let print_arrays fmt  =
  List.iter (fun (_, a, (args_ty, ty)) ->
      fprintf fmt "@{<fg_magenta>array@} @{<fg_red>%a@}[%a] : \
                   @{<fg_green>%a@}@."
        Hstring.print a
        (Pretty.print_list
           (fun fmt -> fprintf fmt "@{<fg_green>%a@}" Hstring.print)
           ",@ ") args_ty
        Hstring.print ty
    )

let print_consts fmt  =
  List.iter (fun (_, c, ty) ->
      fprintf fmt "@{<fg_magenta>const@} @{<fg_blue>%a@} : @{<fg_green>%a@}@."
        Hstring.print c Hstring.print ty
    )

let print_dnf =
   Pretty.print_list
     (fun fmt -> fprintf fmt "@[<hov 4>%a@]" SAtom.print_inline)
     "@ || "
     
let print_init fmt (_, vars, dnf) =
  fprintf fmt "@{<fg_magenta>init@} (%a) {@ %a@ }@,"
    Variable.print_vars vars
    print_dnf dnf

let print_unsafe fmt =
  List.iter (fun (_, vars, u) ->
      fprintf fmt "@{<fg_magenta>unsafe@} (%a) {@ %a@ }@,"
        Variable.print_vars vars
        SAtom.print_inline u
    )

let print_invs fmt =
  List.iter (fun (_, vars, inv) ->
      fprintf fmt "@{<fg_magenta>invariant@} (%a) {@ %a@ }@,"
        Variable.print_vars vars
        SAtom.print_inline inv
    )


let print_reqs fmt (tr_reqs, tr_ureq) =
  if SAtom.for_all Atom.(equal True) tr_reqs && tr_ureq = [] then ()
  else
    fprintf fmt "@{<fg_magenta>requires@} @[<hov 2>{@ %a%a@ }@]@,"
      SAtom.print_inline tr_reqs
      (fun fmt -> List.iter (fun (v, u) ->
           fprintf fmt "@ &&@ @[<hov 1>(@{<fg_magenta>forall_other@} %a.@ %a)@]"
             Variable.print v print_dnf u
         )) tr_ureq

let print_lets fmt tr_lets =
  List.iter (fun (v, t) ->
      fprintf fmt "@[<hov>@{<fg_magenta>let@} %a@ =@ %a@ @{<fg_magenta>in@}@]@,"
        Hstring.print v Term.print t
    ) tr_lets

let print_swts fmt swts =
  match List.rev swts with
  | (_, def) :: rsw ->
    fprintf fmt "@[<v -2>@{<fg_magenta>case@}@,";
    List.iter (fun (c, t) ->
        fprintf fmt "@[<hov 2>| %a :@ %a@]@," SAtom.print_inline c Term.print t
      ) (List.rev rsw);
    fprintf fmt "@[<hov 2>| _ :@ %a@]" Term.print def;
    fprintf fmt "@]"
  | _ -> assert false

let print_assigns fmt tr_assigns =
  List.iter (fun (g, gu) ->
      fprintf fmt "@[<hov>%a@ =@ " Hstring.print g;
      match gu with
      | UTerm t -> fprintf fmt "%a;@]@," Term.print t
      | UCase swts -> fprintf fmt "%a;@]@," print_swts swts
      | URecord _ -> assert false
    ) tr_assigns

let print_updates fmt tr_upds =
  List.iter (fun { up_arr; up_arg; up_swts } ->
      fprintf fmt "@[<hov>%a[%a]@ =@ %a;@]@,"
        Hstring.print up_arr
        Variable.print_vars up_arg
        print_swts up_swts
    ) tr_upds

let print_nondets fmt =
  List.iter (fprintf fmt "%a = ?;@," Hstring.print)

let print_trans fmt =
  List.iter
    (fun { tr_name; tr_args; tr_reqs; tr_ureq; tr_lets;
           tr_assigns; tr_upds; tr_nondets } ->
      fprintf fmt
        "@[<v>@{<fg_magenta>transition@} @{<fg_cyan_b>%a@} (%a)@,\
         %a\
         {@[<v 2>@,\
         %a\
         %a\
         %a\
         %a\
         @]}\
         @,@,@]"
        Hstring.print tr_name
        Variable.print_vars tr_args
        print_reqs (tr_reqs, tr_ureq)
        print_lets tr_lets
        print_assigns tr_assigns
        print_updates tr_upds
        print_nondets tr_nondets
    )


let print_system fmt { type_defs;
                       globals;
                       arrays;
                       consts;
                       init;
                       invs;
                       unsafe;
                       trans } =
  let type_defs, precords =
    List.fold_left (fun (constrs, recs) -> function
      | Constructors i -> i::constrs, recs
      | Records i -> constrs, i::recs
    ) ([],[]) type_defs in
  print_type_defs fmt type_defs;
  pp_print_newline fmt ();
  print_globals fmt globals;
  (* pp_print_newline fmt (); *)
  print_arrays fmt arrays;
  (* pp_print_newline fmt (); *)
  print_consts fmt consts;
  pp_print_newline fmt ();
  print_init fmt init;
  pp_print_newline fmt ();
  print_invs fmt invs;
  pp_print_newline fmt ();
  print_unsafe fmt unsafe;
  pp_print_newline fmt ();
  print_trans fmt (List.rev trans)


let encode_psystem psys =
  let sys = encode_psystem psys in
  if Options.debug then print_system std_formatter sys;
  sys
