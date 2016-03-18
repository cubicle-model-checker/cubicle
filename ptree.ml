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

type pglob_update = PUTerm of term | PUCase of pswts

type pupdate = {
  pup_loc : loc;
  pup_arr : Hstring.t;
  pup_arg : Variable.t list;
  pup_swts : pswts;
}

type ptransition = {
  ptr_name : Hstring.t;
  ptr_args : Variable.t list;
  ptr_reqs : cformula;
  ptr_assigns : (Hstring.t * pglob_update) list;
  ptr_upds : pupdate list;
  ptr_nondets : Hstring.t list;
  ptr_loc : loc;
}

type pregexp = 
    | PEpsilon 
    | PChar of Hstring.t * Hstring.t list
    | PUnion of pregexp list
    | PConcat of pregexp list
    | PStar of pregexp
    | PPlus of pregexp
    | POption of pregexp


type psystem = {
  pglobals : (loc * Hstring.t * Smt.Type.t) list;
  pconsts : (loc * Hstring.t * Smt.Type.t) list;
  parrays : (loc * Hstring.t * (Smt.Type.t list * Smt.Type.t)) list;
  ptype_defs : (loc * Ast.type_constructors) list;
  pinit : loc * Variable.t list * cformula;
  pinvs : (loc * Variable.t list * cformula) list;
  punsafe : (loc * Variable.t list * cformula) list;
  pgood : (loc * Variable.t list * cformula) list;
  ptrans : ptransition list;
  pregexps : pregexp list;
}


type pdecl =
  | PInit of (loc * Variable.t list * cformula)
  | PInv of (loc * Variable.t list * cformula)
  | PUnsafe of (loc * Variable.t list * cformula)
  | PGood of (loc * Variable.t list * cformula)
  | PTrans of ptransition
  | PFun
  | PRegExp of pregexp



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
  | _ -> assert false

let guard_of_formula f =
  match up_quantifiers (dnf f) with
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

let encode_pupdate {pup_loc; pup_arr; pup_arg; pup_swts} =
  {  up_loc = pup_loc;
     up_arr = pup_arr;
     up_arg = pup_arg;
     up_swts = encode_pswts pup_swts;
  }

let encode_ptransition
    {ptr_name; ptr_args; ptr_reqs; ptr_assigns;
     ptr_upds; ptr_nondets; ptr_loc;} =
  let dguards = guard_of_formula ptr_reqs in
  let tr_assigns = List.map (fun (i, pgu) ->
      (i, encode_pglob_update pgu)) ptr_assigns in
  let tr_upds = List.map encode_pupdate ptr_upds in
  List.rev_map (fun (req, ureq) ->
      {  tr_name = ptr_name;
         tr_args = ptr_args;
         tr_reqs = req;
         tr_ureq = ureq;
         tr_assigns;
         tr_upds;
         tr_nondets = ptr_nondets;
         tr_loc = ptr_loc }
    ) dguards

let pregexp_to_simplerl p =
  let rec pr acc = function
    | PEpsilon -> acc
    | PChar (_, vl) -> Hstring.HSet.union (Hstring.HSet.of_list vl) acc
    | PUnion pl | PConcat pl -> List.fold_left pr acc pl
    | PStar p | PPlus p | POption p -> pr acc p in
  let vs = Hstring.HSet.elements (pr Hstring.HSet.empty p) in
  let subst = Variable.all_permutations vs 
    (Variable.give_procs Options.enumerative) in

  let apply_subst s p = 
    let open Regexp.RTrans in
    let rec ar = function
      | PEpsilon -> SEpsilon
      | PChar (n, vl) -> 
        let vl = List.map (Variable.subst s) vl in
        SChar (n, Hstring.HSet.of_list vl)
      | PUnion pl -> SUnion (List.map ar pl)
      | PConcat pl -> SConcat (List.map ar pl)
      | PStar p -> SStar (ar p)
      | PPlus p -> SPlus (ar p)
      | POption p -> SOption (ar p)
    in ar p
  in
  List.map (fun sigma -> apply_subst sigma p) subst
    


let encode_psystem
    {pglobals; pconsts; parrays; ptype_defs;
     pinit = init_loc, init_vars, init_f;
     pinvs; punsafe; pgood; ptrans; pregexps} =
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
  let good =
    List.fold_left (fun acc (good_loc, good_vars, good_f) ->
        let other_vars, dnf = unsafes_of_formula good_f in
        (* List.iter (fun sa -> eprintf "good : %a@." SAtom.print sa) dnf; *)
        let good_vars = good_vars @ other_vars in
        List.fold_left
          (fun acc sa -> (good_loc, good_vars, sa) :: acc) acc dnf
      ) [] pgood
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
  let sregexpl = List.fold_left (fun acc p ->
    let pl = pregexp_to_simplerl p in
    List.rev_append pl acc) [] pregexps in
  
  let regexp = Regexp.RTrans.from_list sregexpl in
  Format.printf "Regexp : %a@." Regexp.RTrans.fprint regexp;
  let automaton = Regexp.Automaton.make_automaton regexp in
  
  {
    globals = pglobals;
    consts = pconsts;
    arrays = parrays;
    type_defs = ptype_defs;
    init;
    invs;
    unsafe;
    good;
    trans;
    automaton;
  }
      


let psystem_of_decls ~pglobals ~pconsts ~parrays ~ptype_defs pdecls =
  let inits, pinvs, punsafe, pgood, ptrans, pregexps =
    List.fold_left (fun (inits, invs, unsafes, goods, trans, regexp) -> function
      | PInit i -> i :: inits, invs, unsafes, goods, trans, regexp
      | PInv i -> inits, i :: invs, unsafes, goods, trans, regexp
      | PGood g -> inits, invs, unsafes, g :: goods, trans, regexp
      | PUnsafe u -> inits, invs, u :: unsafes, goods, trans, regexp
      | PTrans t -> inits, invs, unsafes, goods, t :: trans, regexp
      | PFun -> inits, invs, unsafes, goods, trans, regexp
      | PRegExp re -> inits, invs, unsafes, goods, trans, re::regexp
    ) ([], [], [], [], [], []) pdecls
  in
  let pinit = match inits with
    | [i] -> i
    | [] -> failwith "No inititial formula."
    | _::_ -> failwith "Only one initital formula allowed."
  in
  { pglobals;
    pconsts;
    parrays;
    ptype_defs;
    pinit;
    pinvs;
    punsafe;
    pgood;
    ptrans;
    pregexps;
  }
  
  




(* let rec formula_to_dnf = function *)
(*   | PAtom _ as pa -> pa *)
(*   | PNot f ->  *)
(*   | PAnd of formula * formula *)
(*   | POr of formula * formula *)
(*   | PImp of formula * formula *)
(*   | PIte of formula * formula * formula *)
(*   | PForall of Variable.t list * formula *)
(*   | PExists of Variable.t list * formula *)
(*   | PForall_other of Variable.t list * formula *)
