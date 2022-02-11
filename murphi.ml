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

open Format
open Ast
open Types
open Options
open Util

module A = Atom
module T = Term
module H = Hstring.H

let use_short_names = true
let use_even_shorter_names = true
let use_undefined = true
let use_undef_nondets = false

let proc_type_name = if use_short_names then "N" else "proc"
let state_prefix = if use_short_names then "S" else "state_"
let prev_prefix = if use_short_names then "P" else "prev"
let sprefix prev = if prev then prev_prefix else state_prefix

let array_prefix = "A"
let var_prefix = "V"
let constr_prefix = "C"

let short_names = H.create 47
    
let mk_short_names sys =
  let constrs =
    List.filter (fun c -> c != T.htrue && c != T.hfalse)
      (Smt.Type.all_constructors ()) |> List.rev in
  let cpt = ref 1 in
  List.iter (fun c ->
      let c' = Hstring.make (constr_prefix ^ string_of_int !cpt) in
      incr cpt;
      H.add short_names c c'
    ) constrs;
  cpt := 1;
  List.iter (fun v ->
      let v' = Hstring.make (var_prefix ^ string_of_int !cpt) in
      incr cpt;
      H.add short_names v v'
    ) sys.t_globals;
  cpt := 1;
  List.iter (fun a ->
      let a' = Hstring.make (array_prefix ^ string_of_int !cpt) in
      incr cpt;
      H.add short_names a a'
    ) sys.t_arrays


let letters = [| 'A'; 'B'; 'C'; 'D'; 'E'; 'F'; 'G'; 'H'; 'I'; 'J'; 'K'; 'L';
                 'M'; 'O'; 'Q'; 'R'; 'T'; 'U'; 'V'; 'W'; 'X'; 'Y'; 'Z'|]

let nb_letters = Array.length letters

let next_name =
  let cpt = ref 0 in
  fun () ->
    let d, r = !cpt / nb_letters, !cpt mod nb_letters in
    incr cpt;
    if d = 0 then sprintf "%c" letters.(r)
    else  sprintf "%c%d" letters.(r) d

let mk_shorter_names sys =
  let constrs =
    List.filter (fun c -> c != T.htrue && c != T.hfalse)
      (Smt.Type.all_constructors ()) |> List.rev in
  List.iter (fun n ->
    let f = Hstring.make (next_name ()) in
    H.add short_names n f
  ) (sys.t_globals @ sys.t_arrays @ constrs)


let mk_short_names =
  if use_even_shorter_names then mk_shorter_names else mk_short_names


let rec get_short_term t =
  try match t with
    | Elem(c, Constr) -> Elem(H.find short_names c, Constr) 
    | Elem(v, Glob) -> Elem(H.find short_names v, Glob) 
    | Access(x, xs) -> Access(H.find short_names x, xs)
    | Arith (t', cs) -> Arith (get_short_term t', cs)
    | _ -> t
  with Not_found -> t

let print_list = Pretty.print_list

let print_constants fmt nbprocs abstr =
  fprintf fmt "@[<v 2>const@ ";
  fprintf fmt "PROC_NUM : %d;@ " nbprocs;
  fprintf fmt "ABSTR_NUM : %d;@ " abstr;
  fprintf fmt "@]@."


let print_scalarset fmt num =
  fprintf fmt "scalarset(%s)" num

let print_subrange l fmt num =
  fprintf fmt "%d .. %s" l num

let print_enum fmt constructors =
  let constructors =
    if not use_short_names then constructors
    else
      List.map (fun c -> try H.find short_names c with Not_found -> c)
        constructors in
  fprintf fmt "enum {@[<hov>%a@]}" (print_list Hstring.print ",@ ") constructors

let print_type_def fmt t =
  if t == Smt.Type.type_proc then ()
  else if t == Smt.Type.type_int then
    fprintf fmt "%a : %a;" Hstring.print t (print_subrange 0) "ABSTR_NUM"
  else if t == Smt.Type.type_bool then
    fprintf fmt "%a : boolean;" Hstring.print t
  else if t == Smt.Type.type_real then ()
  else match Smt.Type.constructors t with
  | [] -> (* abstract type *)
    fprintf fmt "%a : %a;" Hstring.print t print_scalarset "ABSTR_NUM"
  | constructors -> (* sum type *)
    fprintf fmt "%a : %a;" Hstring.print t print_enum constructors

let proc_prefix = ref (proc_type_name ^ "_")
let proc_elem = ref proc_type_name

let print_type fmt ty =
  if ty == Smt.Type.type_proc then
    fprintf fmt "%s" !proc_elem
  else Hstring.print fmt ty

let print_type_proc ~proc_ord fmt extra_procs =
  if extra_procs <> [] then begin
    fprintf fmt "p : %a;@ " print_scalarset "PROC_NUM";
    (* proc_prefix := "p_"; *)
    fprintf fmt "%s : union {p, %a};" proc_type_name print_enum extra_procs;
    (* proc_elem := "proc_plus"; *)
  end
  else if proc_ord then begin
    proc_prefix := "";
    fprintf fmt "%s : %a;" proc_type_name (print_subrange 1) "PROC_NUM"
  end
  else
    fprintf fmt "%s : %a;" proc_type_name print_scalarset "PROC_NUM"

let print_types ~proc_ord fmt extra_procs =
  fprintf fmt "@[<v 2>type@ ";
  fprintf fmt "%a@ " (print_type_proc ~proc_ord) extra_procs;
  print_list print_type_def "@ " fmt (Smt.Type.declared_types ());
  fprintf fmt "@]@."


let rec print_var_type fmt = function
  | [], ty -> print_type fmt ty
  | a :: args, ty ->
    fprintf fmt "array [ %a ] of %a"
      print_type a print_var_type (args, ty)

let print_var_def fmt v =
  let ty = Smt.Symbol.type_of v in
  let v =
    if use_short_names then try H.find short_names v with Not_found -> v
    else v
  in
  fprintf fmt "%a : %a;" Hstring.print v print_var_type ty


let print_vars_defs extra_procs fmt l =
  let l = List.filter (fun v -> not (Hstring.list_mem v extra_procs)) l in 
  fprintf fmt "  @[<v 2>STATE : record@ ";
  print_list print_var_def "@ " fmt l;
  fprintf fmt "@]\n  end;@ @.";
  fprintf fmt "@[<v 2>var@ ";
  fprintf fmt "%s : STATE;@ " state_prefix;
  (* fprintf fmt "prev : STATE;@ "; *)
  fprintf fmt "@]@."


let print_access ?(prev=false) fmt (a, args) =
  fprintf fmt "%s.%a" (sprefix prev) Hstring.print a;
  List.iter (fprintf fmt "[%a]" Variable.print) args 
  
let rec print_term' prev fmt = function
  | Elem (b, Constr) when Hstring.equal b T.htrue ->
    fprintf fmt "true"
  | Elem (b, Constr) when Hstring.equal b T.hfalse ->
    fprintf fmt "false"
  | Elem (v, Glob) ->
    fprintf fmt "%s.%a" (sprefix prev) Hstring.print v
  | Access (a, vars) -> print_access ~prev fmt (a, vars)
  | Arith (x, cs) -> fprintf fmt "%a%a" (print_term' prev) x T.print (Const cs)
  | t -> T.print fmt t

let print_term' =
  if not use_short_names then print_term'
  else fun prev fmt t -> print_term' prev fmt (get_short_term t)

let print_term_prev = print_term' true
let print_term = print_term' false


let print_op fmt = function
  | Eq -> fprintf fmt "="
  | Neq -> fprintf fmt "!="
  | Le -> fprintf fmt "<="
  | Lt -> fprintf fmt "<"

let state_vars_of_atom = function
  | A.Comp ((Elem(_, Glob) | Access _ as t1), _,
            (Elem(_, Glob) | Access _ as t2)) ->
    T.Set.add t1 @@ T.Set.singleton t2
  | A.Comp ((Elem(_, Glob) | Access _ as t), _, _)
  | A.Comp (_, _, (Elem(_, Glob) | Access _ as t)) ->
    T.Set.singleton t
  | _ -> T.Set.empty

let print_atom prev fmt = function
  | A.True -> fprintf fmt "true"
  | A.False -> fprintf fmt "false"
  | A.Comp (x, op, y) (* as a *) ->
    (* let vars = state_vars_of_atom a |> T.Set.elements in *)
    (* if vars <> [] then *)
    (*   fprintf fmt "(%a | %a %a %a)" *)
    (*     (print_list *)
    (*        (fun fmt -> fprintf fmt "isundefined(%a)" (print_term' prev)) " | ") vars *)
    (*     (print_term' prev) x print_op op (print_term' prev) y *)
    (*   else *)
    fprintf fmt "%a %a %a" (print_term' prev) x print_op op (print_term' prev) y
  | _ -> assert false


let rec print_atoms prev fmt = print_list (print_atom prev) " &@ " fmt


let print_satom prev fmt sa =
  fprintf fmt "@[<hov>%a@]" (print_atoms prev) (SAtom.elements sa)

let print_satom_prev = print_satom true
let print_satom = print_satom false

let rec print_dnf fmt = print_list print_satom "@ | " fmt


(***************************)
(* Printing initial states *)
(***************************)

let extra_procs acc sa =
  SAtom.fold (fun a acc -> match a with
      | Atom.Comp (Elem(extra, Glob), Neq, Elem(_, Var)) ->
        (* Assume an extra process if a disequality is mentioned on
           type proc in init formula : change this to something more robust *)
        Hstring.HSet.add extra acc
      | _ -> acc) sa acc

let extra_procs_of_sys sys =
  List.fold_left extra_procs Hstring.HSet.empty (snd sys.t_init)
  |> Hstring.HSet.elements

let rec is_const = function
  | Const _ -> true
  | Elem (_, (Var | Constr)) -> true
  | Arith (t, _) -> is_const t
  | _ -> false


module STS = Set.Make(T.Set)

let mk_defined_values sa =
  SAtom.fold (fun a (defined, to_print, related) -> match a with
      | A.Comp ((Elem(v, Glob) | Access (v, _)) as x, Eq, t) when is_const t ->
        let str = asprintf "%a := %a;" print_term x print_term t in
        v :: defined, str :: to_print, related
      | A.Comp (((Elem(_, Glob) | Access _) as x1), Eq,
                ((Elem(_, Glob) | Access _) as x2)) ->
        (* poor man uf *)
        let rels, related = STS.fold (fun r (rels, related) ->
            if T.Set.mem x1 r || T.Set.mem x2 r then
              T.Set.union r rels, STS.remove r related
            else rels, related
          ) related (T.Set.add x1 (T.Set.singleton x2), related) in
        defined, to_print, STS.add rels related

      (* | Atom.Comp (Elem(extra, Glob), Neq, Elem(_, Var)) -> *)
      (*   (\* Assume an extra process if a disequality is mentioned on *)
      (*      type proc in init formula : change this to something more robust *\) *)
      (*   eprintf "\n\nDEFINED: %a\n@." Hstring.print extra; *)
      (*   extra :: defined, to_print, related *)

      | A.True -> defined, to_print, related
      | A.False -> raise Exit
      | A.Ite _ -> assert false
      | _ -> defined, to_print, related
    ) sa ([], [], STS.empty)

module SM = Map.Make(String)

let mk_fresh =
  let i = ref 0 in
  let p_proc = "p_proc" in
  fun ty ->
    (* create only one proc fresh variable for init *)
    if ty == Smt.Type.type_proc then p_proc
    else begin
      incr i;
      "d" ^ string_of_int !i ^ "_" ^ asprintf "%a" print_type ty
    end
    

let mk_related_init_values =
  STS.fold (fun rel (defined, to_print, freshs) ->
      let ty = T.type_of (T.Set.choose rel) in
      let f = mk_fresh ty in
      let defined, to_print =
        T.Set.fold (fun x (defined, to_print) ->
            match x with
            | Elem (v, _) | Access (v, _) ->
              v :: defined,
              asprintf "%a := %s;" print_term x f :: to_print
            | _ -> assert false
          ) rel (defined, to_print) in

      defined, to_print, SM.add f ty freshs
    )

let shrink_to x y =
  let rec aux acc x y = match x, y with
    | _, [] -> List.rev acc
    | a::r, _::u -> aux (a :: acc) r u
    | [], _ -> assert false
  in
  aux [] x y

let mk_undefinied_init_values qvars defined =
  List.fold_left (fun (to_print, freshs) v ->
      if Hstring.list_mem v defined then to_print, freshs
      else
        let args, ty = Smt.Symbol.type_of v in
        let t = match args with
          | [] -> Elem (v, Glob)
          | _ -> Access (v, shrink_to qvars args) in
        (* if ty != Smt.Type.type_proc && Smt.Type.constructors ty <> [] then *)
        (*     asprintf "clear %a;" print_term t :: to_print, freshs *)
        (* else *)
        if use_undefined then
          if ty == Smt.Type.type_proc || Smt.Type.constructors ty = [] then
            asprintf "undefine %a;" print_term t :: to_print, freshs
          else
            asprintf "clear %a;" print_term t :: to_print, freshs
        else
          let f = mk_fresh ty in
          asprintf "%a := %s;" print_term t f :: to_print,
          SM.add f ty freshs
    )


let rec print_init_freshs fmt = function
  | [] -> assert false
  | [f, ty] ->
      fprintf fmt "%s : %a" f print_type ty
  | (f, ty) :: rf ->
    fprintf fmt "%s : %a;@ %a" f print_type ty print_init_freshs rf


let print_init_startstate fmt freshs init_name =
  if SM.is_empty freshs then begin
    fprintf fmt "@[<v 2>startstate \"%s\"@ " init_name;
    fun () -> fprintf fmt "@]@ end;@."
  end
  else begin
    fprintf fmt "@[<v 2>ruleset @[<hov>%a@] do startstate \"%s\"@ "
      print_init_freshs (SM.bindings freshs) init_name;
    fun () -> fprintf fmt "@]@ end end;@."
  end


let print_for fmt qv =
  fprintf fmt "@[<v 2>for %a : %s do@ " Variable.print qv proc_type_name;
  fun () -> fprintf fmt "@]@ end;"


let print_fors fmt qvars =
  List.fold_left (fun close qv ->
      let close_for = print_for fmt qv in
      fun () -> close_for (); close ()
    ) (fun () -> ()) qvars


let print_init globals arrays qvars fmt sa =
  let qsa, gsa =
    SAtom.partition (fun a ->
        let va = Atom.variables a in
        List.exists (fun qv -> Variable.Set.mem qv va) qvars
      ) sa in

  (* initial values for quantified part *)
  let defined_q, to_print_q, related_q = mk_defined_values qsa in
  (* initial values for unquantified part *)
  let defined_g, to_print_g, related_g = mk_defined_values gsa in
  let defined = List.rev_append defined_q defined_g in
  
  (* initial values for quantified part *)
  let defined, to_print_q, freshs =
    mk_related_init_values related_q (defined, to_print_q, SM.empty) in
  let to_print_q, freshs =
    mk_undefinied_init_values qvars defined (to_print_q, freshs) arrays in

  (* initial values for unquantified part *)
  let defined, to_print_g, freshs =
    mk_related_init_values related_g (defined, to_print_g, freshs) in
  let to_print_g, freshs =
    mk_undefinied_init_values qvars defined (to_print_g, freshs) globals in

  let close_startstate = print_init_startstate fmt freshs "Init" in
  let close_fors = print_fors fmt qvars in
  print_list pp_print_string "@ " fmt to_print_q;
  close_fors ();
  if to_print_g <> [] then fprintf fmt "@ ";
  print_list pp_print_string "@ " fmt to_print_g;
  close_startstate ()
   

let print_inits fmt { t_globals; t_arrays; t_init = qvars, inits } =
  List.iter (fprintf fmt "%a@." (print_init t_globals t_arrays qvars)) inits



(************************)
(* Printing transitions *)
(************************)

let print_swts ot fmt swts =
  let rec sd acc = function
    | [] -> assert false
    | [d] -> acc, d
    | s::r -> sd (s::acc) r in
  let swts, (_, default) = sd [] swts in
  if swts = [] then
    fprintf fmt "%a := %a" print_term ot print_term_prev default
  else begin
    fprintf fmt "@[<hov 2>if ";
    let first = ref true in
    List.iter (fun (cond, t) ->
        if not !first then fprintf fmt "@[<hov 2>elsif ";
        fprintf fmt "%a then@ %a := %a@]@ "
          print_satom_prev cond print_term ot print_term_prev t;
        first := false
      ) swts;
    fprintf fmt "@[<hov 2>else@ %a := %a@]@ "
      print_term ot print_term_prev default;
    fprintf fmt "endif;"
  end


let print_assign fmt (v, up) =
  let tv = Elem (v, Glob) in
  match up with
  | UTerm t ->
    fprintf fmt "%a := %a;" print_term (Elem(v,Glob)) print_term_prev t
  | UCase swts -> print_swts tv fmt swts

let print_assigns fmt = List.iter (fprintf fmt "%a@ " print_assign)


let print_update fmt { up_arr; up_arg; up_swts } =
  let ta = Access(up_arr, up_arg) in
  let close_fors = print_fors fmt up_arg in
  print_swts ta fmt up_swts;
  close_fors ()

let print_updates fmt = List.iter (fprintf fmt "%a@ " print_update)

let print_nondet cpt fmt v =
  fprintf fmt "%a := d%d;" print_term (Elem(v,Glob)) cpt

let print_nondets ndts =
  let cpt = ref 0 in
  print_list (fun n -> incr cpt; print_nondet !cpt n) "@ " ndts

let print_nondet_undef fmt v =
  let _, ty = Smt.Symbol.type_of v in
  if ty == Smt.Type.type_proc || Smt.Type.constructors ty = [] then
    fprintf fmt "undefine %a;" print_term (Elem(v,Glob))
  else
    fprintf fmt "clear %a;" print_term (Elem(v,Glob))

let print_nondets_undef = print_list print_nondet_undef "@ "

let print_nondets =
  if use_undef_nondets then print_nondets_undef else print_nondets

let print_forall fmt qv =
  fprintf fmt "@[<v 2>forall %a : %s do@ " Variable.print qv proc_type_name;
  fun () -> fprintf fmt "@]@ end"


let print_foralls fmt qvars =
  List.fold_left (fun close qv ->
      let close_forall = print_forall fmt qv in
      fun () -> close_forall (); close ()
    ) (fun () -> ()) qvars


let rec print_is_other fmt (v, args) = match args with
  | [] -> ()
  | [a] -> fprintf fmt "%a != %a -> " Variable.print v Variable.print a
  | a :: ra ->
    fprintf fmt "%a != %a &@ %a" Variable.print v Variable.print a
      print_is_other (v, ra)
  

let print_forall_other args fmt (v, dnf) =
  let close_forall = print_forall fmt v in
  print_is_other fmt (v, args);
  fprintf fmt "(%a)" print_dnf dnf;
  close_forall ()


let rec print_ureqs args fmt = function
  | [] -> ()
  | [u] -> print_forall_other args fmt u
  | u :: ru ->
    fprintf fmt "%a@ &@ %a" (print_forall_other args) u (print_ureqs args) ru


let print_guard fmt { tr_args; tr_reqs; tr_ureq } =
  (* fprintf fmt "  @[<v>"; *)
  print_satom fmt tr_reqs;
  if tr_ureq <> [] && not(SAtom.is_empty tr_reqs) then fprintf fmt " &@ ";
  print_ureqs tr_args fmt tr_ureq
  (* fprintf fmt "@]\n" *)


let make_mu_trans_args args nondets =
  let acc =
    List.fold_left (fun acc v ->
      (v, !proc_elem) :: acc
      ) [] args
  in
  let _, acc =
    List.fold_left (fun (cpt, acc) v ->
      let d = Hstring.view (snd (Smt.Symbol.type_of v)) in
      let dv = Hstring.make ("d" ^ string_of_int cpt) in
      cpt + 1, (dv, d) :: acc
      ) (1, acc) nondets
  in
  List.rev acc
      

let rec print_trans_args fmt = function
  | [] -> assert false
  | [v, d] -> fprintf fmt "%a : %s" Variable.print v d
  | (v, d) :: args ->
    fprintf fmt "%a : %s;@ %a" Variable.print v d print_trans_args args

  
let rec distinct acc seen procs = match procs with
  | [] -> acc
  | p :: r ->
    let acc = List.fold_left (fun acc p' ->
        (p', p) :: acc
      ) acc seen in
    distinct acc (p :: seen) r


let print_distinct_args fmt args =
  let pairs = distinct [] [] args in
  if pairs <> [] then
    let rec print_pairs fmt = function
      | [] -> ()
      | [x, y] -> fprintf fmt "%a != %a" Variable.print x Variable.print y
      | (x, y) :: r ->
        fprintf fmt "%a != %a &@ %a"
          Variable.print x Variable.print y print_pairs r
    in
    fprintf fmt "@[<hov>%a@] &@ " print_pairs pairs


let print_ruleset fmt args nondets trans_name =
  let all_args_ty =
    make_mu_trans_args args (if use_undef_nondets then [] else nondets) in
  if all_args_ty = [] then begin
    fprintf fmt "@[<v 2>rule \"%s\"@ " trans_name;
    fun () -> fprintf fmt "@]@ end;@."
  end
  else begin
    fprintf fmt "@[<v 2>ruleset @[<hov>%a@] do rule \"%s\"@ "
      print_trans_args all_args_ty trans_name;
    print_distinct_args fmt args;
    fun () -> fprintf fmt "@]@ end end;@."
  end


let print_actions fmt t =
  fprintf fmt "@[<v 2>var@ %s : STATE;@]@ " prev_prefix;
  fprintf fmt "@[<v 2>begin@ %s := %s;@ --@ " prev_prefix state_prefix;
  fprintf fmt "%a%a%a"
    print_assigns t.tr_assigns
    print_updates t.tr_upds
    print_nondets t.tr_nondets;
  fprintf fmt "@]"


let print_transition fmt t =
  let args = t.tr_args in
  let close_ruleset =
    print_ruleset fmt args t.tr_nondets (Hstring.view t.tr_name) in
  print_guard fmt t;
  fprintf fmt "@]@.@[<v 2>==>@ ";
  print_actions fmt t;
  close_ruleset ()


let rec print_alias fmt v =
  fprintf fmt "prev_%a : %a" Hstring.print v  Hstring.print v

let print_aliases fmt variables =
  if variables = [] then begin
    fun () -> ()
  end
  else begin
    fprintf fmt "@[<v 2>alias @[<hov>%a@] do@ "
      (print_list print_alias ";@ ") variables;
    fun () -> fprintf fmt "@]@ endalias;@."
  end

let print_transitions globals arrays fmt trans =
  (* let close_aliases = print_aliases fmt (globals @ arrays) in  *)
  List.iter (fun t -> fprintf fmt "%a\n" print_transition t.tr_info) trans
  (* close_aliases () *)
    

(********************************************)
(* Printing unsafe properties as invariants *)
(********************************************)

let print_invariant fmt name =
  fprintf fmt "@[<v 2>invariant \"%s\"@ " name;
  fun () -> fprintf fmt "@];@."


  
let print_if_distinct fmt procs =
  let pairs = distinct [] [] procs in
  let rec print_pairs fmt = function
    | [] -> ()
    | [x, y] -> fprintf fmt "%a != %a -> " Variable.print x Variable.print y
    | (x, y) :: r ->
      fprintf fmt "%a != %a &@ %a"
        Variable.print x Variable.print y print_pairs r
  in
  print_pairs fmt pairs

let state_vars_of_unsafe sa =
  SAtom.fold (fun a acc ->
      T.Set.union acc (state_vars_of_atom a)
    ) sa T.Set.empty

let print_not_undefined args fmt sa =
  let tvs = state_vars_of_unsafe sa in
  if not (T.Set.is_empty tvs) then
    let rec print_notundef fmt = function
      | [] -> ()
      | [t] ->
        fprintf fmt "!isundefined(%a) %s " print_term t
          (match args with _::_::_ -> "&" | _ -> "->")
      | t :: r ->
        fprintf fmt "!isundefined(%a) &@ %a" print_term t print_notundef r
    in
    print_notundef fmt (T.Set.elements tvs)


let print_unsafe =
  let cpt = ref 1 in
  fun fmt (procs, sa) ->
    let rprocs = List.map (fun p ->
        let p' = Bytes.of_string (Hstring.view p) in
        Bytes.set p' 0 'p';
        Hstring.make (Bytes.to_string p')
      ) procs in
    let sigma = List.combine procs rprocs in
    let renamed_sa = SAtom.subst sigma sa in
    let close_invariant =
      print_invariant fmt ("unsafe[" ^ string_of_int !cpt ^ "]") in
    incr cpt;
    let close_foralls = print_foralls fmt rprocs in
    print_not_undefined rprocs fmt renamed_sa;
    print_if_distinct fmt rprocs;
    fprintf fmt "!(@[<hov>%a@])" print_satom renamed_sa;
    close_foralls ();
    close_invariant ();
    fprintf fmt "@."


let print_unsafes fmt =
  List.iter (fun {cube = {Cube.vars; litterals}} ->
      fprintf fmt "%a\n" print_unsafe (vars, litterals))


(***********************************************)
(* Murphi version of cubicle transition system *)
(***********************************************)

(* Removing uderscores which Murphi does not support *)

let remove_underscores_update u =
  let sigma = List.fold_left (fun sigma j ->
      let sj = Hstring.view j in
      if sj.[0] = '_' then
        let j' = Hstring.make (String.sub sj 1 (String.length sj - 1)) in
        (j, j') :: sigma
      else sigma
    ) [] u.up_arg
  in
  if sigma = [] then u
  else
    let arg = List.map (Variable.subst sigma) u.up_arg in
    let swts =
      List.map (fun (c, t) -> SAtom.subst sigma c, Term.subst sigma t) u.up_swts
    in
    { u with up_arg = arg; up_swts = swts }


let remove_underscores_trans t =
  { t with
    tr_info =
      { t.tr_info with
        tr_upds = List.map remove_underscores_update t.tr_info.tr_upds }}

let remove_underscores sys =
  { sys with t_trans = List.map remove_underscores_trans sys.t_trans }


(* Checking if the system uses the fact that processes are ordered *)

let ordered_procs_atom = function
  | A.Comp (Elem(_, Var), (Le | Lt), _)
  | A.Comp (_, (Le | Lt), Elem(_, Var)) -> true
  | A.Comp (x, (Le | Lt), y) when
      Term.type_of x == Smt.Type.type_proc ||
      Term.type_of y == Smt.Type.type_proc -> true
  | _ -> false

let ordered_procs_satom = SAtom.exists ordered_procs_atom
let ordered_procs_node_cube n = ordered_procs_satom n.cube.Cube.litterals
let ordered_procs_dnf = List.exists ordered_procs_satom
let ordered_procs_swts = List.exists (fun (c, _) -> ordered_procs_satom c)
let ordered_procs_globu = function
  | UTerm _ -> false
  | UCase swts -> ordered_procs_swts swts
let ordered_procs_up u = ordered_procs_swts u.up_swts

let ordered_procs_trans { tr_info = t } =
  ordered_procs_satom t.tr_reqs
  || List.exists (fun (_, dnf) -> ordered_procs_dnf dnf) t.tr_ureq
  || List.exists (fun (_, gu) -> ordered_procs_globu gu) t.tr_assigns
  || List.exists ordered_procs_up t.tr_upds

let ordered_procs_sys s =
  ordered_procs_dnf (snd s.t_init)
  || List.exists ordered_procs_node_cube s.t_invs
  || List.exists ordered_procs_node_cube s.t_unsafe
  || List.exists ordered_procs_trans s.t_trans


(* Pretty printing system in Murphi syntax *)

let print_system nbprocs abstr fmt sys =
  if use_short_names then mk_short_names sys;
  let sys = remove_underscores sys in
  let proc_ord = ordered_procs_sys sys in
  print_constants fmt nbprocs abstr; pp_print_newline fmt ();
  print_types ~proc_ord fmt []; pp_print_newline fmt ();
  print_vars_defs [] fmt (sys.t_globals @ sys.t_arrays);
  pp_print_newline fmt ();
  print_inits fmt sys; pp_print_newline fmt ();
  print_transitions sys.t_globals sys.t_arrays fmt sys.t_trans;
  print_unsafes fmt sys.t_unsafe



(*****************)
(* Murphi oracle *)
(*****************)


let mk_encoding_table eenv nbprocs abstr sys =
  let table = Muparser_globals.encoding in
  let procs = Variable.give_procs nbprocs in
  let var_terms = Forward.all_var_terms procs sys |> Term.Set.elements in
  let constr_terms =
    List.rev_map (fun x -> Elem (x, Constr)) (Smt.Type.all_constructors ()) in
  let proc_terms = List.map (fun x -> Elem (x, Var)) procs in
  
  let imp = ref 1 in
  let mu_procs =
    List.map (fun _ ->
        let mup = Hstring.make (!proc_prefix ^ string_of_int !imp) in
        incr imp;
        mup
      ) procs in

  let mu_sigma = List.combine procs mu_procs in
  let mu_var_terms = List.map (Term.subst mu_sigma) var_terms in
  let mu_constr_terms = constr_terms in (* no need to apply mu_sigma *)
  let mu_proc_terms = List.map (Term.subst mu_sigma) proc_terms in
  let mu_cub_terms =
    List.combine
      (mu_var_terms @ mu_constr_terms @ mu_proc_terms)
      (var_terms @ constr_terms @ proc_terms) in
  
  (* let nbterms = *)
  (*   List.(length var_terms + length constr_terms + length proc_terms) in *)
  List.iter (fun (mu, t) ->
      let s = asprintf "%a" print_term mu in
      let id = Enumerative.int_of_term eenv t in
      (* eprintf "adding %s -> %d@." s id; *)
      Hashtbl.add table s id
    ) mu_cub_terms;
  let eid = ref (Enumerative.next_id eenv) in
  List.iter (fun ty ->
      if ty != Smt.Type.type_bool &&
         ty != Smt.Type.type_int &&
         ty != Smt.Type.type_real &&
         ty != Smt.Type.type_proc &&
         Smt.Type.constructors ty = [] then
        for i = 1 to abstr do
          let s = Hstring.view ty ^ "_" ^ string_of_int i in
          (* eprintf "adding %s -> %d@." s !eid; *)
          Hashtbl.add table s !eid;
          incr eid
        done
    ) (Smt.Type.declared_types ());
  (* adding undefined value *)
  Hashtbl.add table "Undefined" (-1)
  


let init_parser nbprocs abstr sys =
  let eenv = Enumerative.mk_env nbprocs sys in
  Muparser_globals.env := eenv;
  mk_encoding_table eenv nbprocs abstr sys;
  eenv

(* failed attempt at a simpler parser for murphi's output *)
let simple_parser ic =
  let open Scanf in
  let open Muparser_globals in
  let print_mu = ref debug in
  try
    while true do
      let l = input_line ic in
      (* eprintf ">>%s@." l; *)
      (if String.length l <> 0 then
        try  (* eprintf "st?."; *)
          sscanf l "State %d:" (fun d ->
              (* eprintf "state %d@." d; *)
              if max_forward <> -1 && d > max_forward then
                Unix.kill (Unix.getpid ()) Sys.sigint
              else
                begin
                  Muparser_globals.new_state ();
                  try while true do
                      let l = input_line ic in
                      (* eprintf ">>>>%s@." l; *)
                      if String.length l = 0 then
                        ((* eprintf "<< !!!@."; *) raise Exit)
                      else
                      sscanf l "%s@:%s"
                        (fun v x -> try
                            (* eprintf "  %s -> %s@." v x; *)
                            let id_var = Hashtbl.find encoding v in
                            let id_value = Hashtbl.find encoding x in
                            let si = Enumerative.state_as_array !st in
                            si.(id_var) <- id_value
                          with Not_found -> ())
                    done;
                  with Exit -> Enumerative.register_state !env !st
                end)
        with End_of_file -> raise End_of_file
           | _ ->
             try (* eprintf "pr?."; *)
               sscanf l "Progress Report:" (print_mu := true)
             with _ -> if !print_mu then printf "%s\n" l)
      (* ; eprintf "fin@."; *)
    done
  with Exit | End_of_file -> ()

(*****************************)
(* Interruptions with Ctrl-C *)
(*****************************)

let install_sigint pid =
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ ->
          printf "\nKilling Murphi process pid %d@." pid;
          Unix.kill pid Sys.sigterm;
          printf "@{<b>@{<fg_red>ABORTING MURPHI!@}@} \
                  Received SIGINT@.";
          printf "Finalizing search.\n@.";
          raise Exit;
       ))


let report_cmd_status name st out err =
  match st with
  | Unix.WEXITED 0 ->
    if not quiet then printf "@{<b>[@{<fg_green>OK@}]@}@.";
    if debug || verbose > 0 then
      printf "@{<fg_green>%s exited correctly@}@." name
  | Unix.WEXITED c ->
    eprintf "@{<fg_red>%s failure@} murphi exited with status %d@." name c;
    eprintf "@{<b>%s standard output:@}\n%s\n\
             @{<b>%s error output:@}\n%s@."
      name out name err;
    exit c
  | Unix.WSIGNALED s ->
    if debug || verbose > 0 then
      printf "@{<fg_red>%s killed@} by signal %d@." name s;
    exit 1
  | Unix.WSTOPPED s -> (* Stopped by signal *)
    if debug || verbose > 0 then
      printf "@{<fg_red>%s stopped@} by signal %d@." name s;
    exit 1


(****************************************)
(* Oracle interface (see {!Oracle.Sig}) *)
(****************************************)

let split_string s =
  let i = ref 0 in
  let n = String.length s in
  let l = ref [] in
  while !i < n do
    let j = try String.index_from s !i ' ' with Not_found -> n in
    let x, y = !i, j - !i in
    if y <> 0 then l := String.sub s x y :: !l;
    i := j + 1
  done;
  Array.of_list (List.rev !l)


(* Print states and don't check for deadlock by default *)
let muexe_opts = Array.concat [
    [| "-ta"; "-ndl" |];
    if verbose > 0 then [|"-tf"|] else [||];
    split_string murphi_uopts
  ]
    

let init sys =

  (* let extra_procs = extra_procs_of_sys sys in *)
  let nbprocs = enumerative (* + List.length extra_procs *) in
  let abstr = 1 in

  let bname = Filename.basename file in
  let name =
    try Filename.chop_extension bname
    with Invalid_argument _ -> bname in
  (* Temporary file for writing murphi system *)
  let mu_tmp = Filename.temp_file name ".m" in
  (* let tmp_dir = Filename.dirname mu_tmp in *)
  (* let mu_base = Filename.basename mu_tmp in *)
  let mu_chop = Filename.chop_extension mu_tmp in
  let mu_cpp = mu_chop  ^ ".cpp" in
  let mu_exe = mu_chop in

  let mu_ch = open_out mu_tmp in
  let mu_fmt = formatter_of_out_channel mu_ch in

  (* print_system nbprocs abstr std_formatter sys; exit 1; *)
  
  print_system nbprocs abstr mu_fmt sys;
  
  (* Close murphi file *)
  close_out mu_ch;

  if debug || verbose > 0 then printf "Murphi system generated in %s@." mu_tmp;

  let enum_env = init_parser nbprocs abstr sys in

  (* Running murphi compiler *)
  if not quiet then printf "Running murphi compiler @?";
  let mu_to_cpp_out, mu_to_cpp_err, mu_to_cpp_status  =
    syscall_full (String.concat " " [mu_cmd; mu_opts; mu_tmp]) in

  report_cmd_status (sprintf "Murphi (%s)" mu_cmd)
    mu_to_cpp_status mu_to_cpp_out mu_to_cpp_err;
  
  (* Running C compiler *)
  if not quiet then printf "Running C++ compiler @?";
  let cpp_out, cpp_err, cpp_status =
    syscall_full (String.concat " " [cpp_cmd; "-o"; mu_exe; mu_cpp]) in

  report_cmd_status (sprintf "C++ compiler (%s)" cpp_cmd)
    cpp_status cpp_out cpp_err;

  
  (* Create pipes for input, output and error output *)
  let muexe_stdin_in, muexe_stdin_out = Unix.pipe () in
  let muexe_stdout_in, muexe_stdout_out = Unix.pipe () in 
  let muexe_stderr_in, muexe_stderr_out = Unix.pipe () in 

  let muexe_cmd = Array.append [| mu_exe |] muexe_opts in

  if not quiet then
    printf "Model checking murphi model @{<b>%s@}@." (Filename.basename mu_exe);
  
  (* Create muexe process that will run in parallel *)
  let muexe_pid = 
    Unix.create_process mu_exe muexe_cmd
      muexe_stdin_in muexe_stdout_out muexe_stderr_out in

  (* Close Cubicle's end of the pipe which has been duplicated by the Muprhi
     process *)
  Unix.close muexe_stdin_in;
  Unix.close muexe_stdout_out; 
  Unix.close muexe_stderr_out; 

  install_sigint muexe_pid;

  (try
     (* Get an output channel to read from murphi's stdout *)
     let muexe_stdout_ch = Unix.in_channel_of_descr muexe_stdout_in in

     (* Create a lexing buffer on murphi's stdout *)
     let muexe_lexbuf = Lexing.from_channel muexe_stdout_ch in

     (* Parse the ouptut of the executable created by murphi.
        This populates automatically the states in {!Enumerative}. *)
     Muparser.states Mulexer.token muexe_lexbuf;
     (* simple_parser muexe_stdout_ch; *)

     (* Wait for the murphi process to terminate *)
     let _, muexe_status = Unix.waitpid [] muexe_pid in

     (* Check termination status of muexe *)
     begin match muexe_status with
       | Unix.WEXITED 0 -> (* Exit with code *)
         if debug then printf "@{<fg_green>Murphi exited correctly@}@."
       | Unix.WEXITED c -> (* Exit with code *)
         if not quiet then printf "@{<fg_red>Murphi exited with code %d@}@." c
       | Unix.WSIGNALED s -> (* Killed by signal *)
         if not quiet then printf "@{<fg_red>Murphi killed@} by signal %d@." s
       | Unix.WSTOPPED s -> (* Stopped by signal *)
         if not quiet then
           printf "@{<fg_yellow>Murphi stopped@} by signal %d@." s
     end;
   with
     Exit -> (* We killed murphi ourselves *) ());

  Enumerative.no_scan_states enum_env;
  
  (* Close file descriptors of murphi *)
  Unix.close muexe_stdin_out;
  Unix.close muexe_stdout_in;
  Unix.close muexe_stderr_in;

  (* Do subtyping at the end of the run of murphi as it does not support
     redefinitions of subtypes or intersecting subtypes *)
  if subtyping then begin
    Smt.Variant.close ();
    if debug then Smt.Variant.print ()
  end
  



(* Use the checking of candidates implemented by Enumerative *)

let first_good_candidate = Enumerative.first_good_candidate
