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



let rec print_list print sep fmt = function
  | [] -> ()
  | [e] -> print fmt e
  | e :: l ->
    print fmt e;
    fprintf fmt sep;
    print_list print sep fmt l

let print_constants fmt nbprocs abstr =
  fprintf fmt "@[<v 2>const@ ";
  fprintf fmt "PROC_NUM : %d;@ " nbprocs;
  fprintf fmt "ABSTR_NUM : %d;@ " abstr;
  fprintf fmt "@]@."


let print_scalarset fmt num =
  fprintf fmt "scalarset(%s)" num

let print_subrange fmt num =
  fprintf fmt "0 .. %s" num

let print_enum fmt constructors =
  fprintf fmt "enum {@[<hov>%a@]}" (print_list Hstring.print ",@ ") constructors


let print_type fmt t =
  if t == Smt.Type.type_proc then
    fprintf fmt "%a : %a;" Hstring.print t print_scalarset "PROC_NUM"
  else if t == Smt.Type.type_int then
    fprintf fmt "%a : %a;" Hstring.print t print_subrange "ABSTR_NUM"
  else if t == Smt.Type.type_bool then
    fprintf fmt "%a : boolean;" Hstring.print t
  else if t == Smt.Type.type_real then ()
  else match Smt.Type.constructors t with
  | [] -> (* abstract type *)
    fprintf fmt "%a : %a;" Hstring.print t print_scalarset "ABSTR_NUM"
  | constructors -> (* sum type *)
    fprintf fmt "%a : %a;" Hstring.print t print_enum constructors


let print_types fmt () =
  fprintf fmt "@[<v 2>type@ ";
  print_list print_type "@ " fmt (Smt.Type.declared_types ());
  fprintf fmt "@]@."


let rec print_var_type fmt = function
  | [], ty -> fprintf fmt "%a" Hstring.print ty
  | a :: args, ty ->
    fprintf fmt "array [ %a ] of %a"
      Hstring.print a print_var_type (args, ty)

let print_var_def fmt v =
  let ty = Smt.Symbol.type_of v in
  fprintf fmt "%a : %a;" Hstring.print v print_var_type ty


let print_vars_defs fmt l =
  fprintf fmt "@[<v 2>var@ ";
  print_list print_var_def "@ " fmt l;
  fprintf fmt "@]@."


let print_access fmt (a, args) =
  fprintf fmt "%a" Hstring.print a;
  List.iter (fprintf fmt "[%a]" Variable.print) args 
  
let print_term fmt = function
  | Elem (b, Constr) when Hstring.equal b T.htrue ->
    fprintf fmt "true"
  | Elem (b, Constr) when Hstring.equal b T.hfalse ->
    fprintf fmt "false"
  | Access (a, vars) -> print_access fmt (a, vars)
  | t -> T.print fmt t


let print_op fmt = function
  | Eq -> fprintf fmt "="
  | Neq -> fprintf fmt "!="
  | Le -> fprintf fmt "<="
  | Lt -> fprintf fmt "<"


let print_atom fmt = function
  | A.True -> fprintf fmt "true"
  | A.False -> fprintf fmt "false"
  | A.Comp (x, op, y) ->
    fprintf fmt "%a %a %a" print_term x print_op op print_term y
  | _ -> assert false


let rec print_atoms fmt = print_list print_atom " &@ " fmt


let print_satom fmt sa =
  fprintf fmt "@[<hov>%a@]" print_atoms (SAtom.elements sa)

let rec print_dnf fmt = print_list print_satom "@ | " fmt


(***************************)
(* Printing initial states *)
(***************************)

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
      | A.True -> defined, to_print, related
      | A.False -> raise Exit
      | A.Ite _ -> assert false
      | _ -> defined, to_print, related
    ) sa ([], [], STS.empty)


let mk_fresh =
  let i = ref 0 in
  fun ty ->
    incr i;
    "d" ^ string_of_int !i ^ "_" ^ Hstring.view ty


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

      defined, to_print, (f, ty) :: freshs
    )


let mk_undefinied_init_values qvars defined =
  List.fold_left (fun (to_print, freshs) v ->
      if Hstring.list_mem v defined then to_print, freshs
      else
        let args, ty = Smt.Symbol.type_of v in
        let f = mk_fresh ty in
        let t = match args with
          | [] -> Elem (v, Glob)
          | _ -> Access (v, qvars) in
        asprintf "%a := %s;" print_term t f :: to_print,
        (f, ty) :: freshs
    )


let rec print_init_freshs fmt = function
  | [] -> assert false
  | [f, ty] -> fprintf fmt "%s : %a" f Hstring.print ty
  | (f, ty) :: rf ->
    fprintf fmt "%s : %a;@ %a" f Hstring.print ty print_init_freshs rf


let print_init_startstate fmt freshs init_name =
  if freshs = [] then begin
    fprintf fmt "@[<v 2>startstate \"%s\"@ " init_name;
    fun () -> fprintf fmt "@]@ end;@."
  end
  else begin
    fprintf fmt "@[<v 2>ruleset @[<hov>%a@] do startstate \"%s\"@ "
      print_init_freshs freshs init_name;
    fun () -> fprintf fmt "@]@ end end;@."
  end


let print_for fmt qv =
  fprintf fmt "@[<v 2>for %a : proc do@ " Variable.print qv;
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
  let defined_q, to_print_q, freshs =
    mk_related_init_values related_q (defined_q, to_print_q, []) in
  let to_print_q, freshs =
    mk_undefinied_init_values qvars defined_q (to_print_q, freshs) arrays in

  (* initial values for unquantified part *)
  let defined_g, to_print_g, related_g = mk_defined_values gsa in
  let defined_g, to_print_g, freshs =
    mk_related_init_values related_g (defined_g, to_print_g, freshs) in
  let to_print_g, freshs =
    mk_undefinied_init_values qvars defined_g (to_print_g, freshs) globals in

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
    fprintf fmt "%a := %a" print_term ot print_term default
  else begin
    fprintf fmt "@[<hov>if ";
    let first = ref true in
    List.iter (fun (cond, t) ->
        if not !first then fprintf fmt "elsif ";
        fprintf fmt "%a then@ %a := %a@ "
          print_satom cond print_term ot print_term t;
        first := false
      ) swts;
    fprintf fmt "else@ %a := %a@]@ " print_term ot print_term default;
    fprintf fmt "endif;"
  end


let print_assign fmt (v, up) =
  let tv = Elem (v, Glob) in
  match up with
  | UTerm t -> fprintf fmt "%a := %a;" Hstring.print v print_term t
  | UCase swts -> print_swts tv fmt swts

let print_assigns fmt = List.iter (fprintf fmt "%a@ " print_assign)


let print_update fmt { up_arr; up_arg; up_swts } =
  let ta = Access(up_arr, up_arg) in
  let close_fors = print_fors fmt up_arg in
  print_swts ta fmt up_swts;
  close_fors ()

let print_updates fmt = List.iter (fprintf fmt "%a@ " print_update)

let print_nondet fmt v =
  fprintf fmt "undefine %a;" Hstring.print v

let print_nondets = print_list print_nondet "@ "


let print_forall fmt qv =
  fprintf fmt "@[<v 2>forall %a : proc do@ " Variable.print qv;
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


let rec print_trans_args fmt = function
  | [] -> assert false
  | [v] -> fprintf fmt "%a : proc" Variable.print v
  | v :: args ->
    fprintf fmt "%a : proc;@ %a" Variable.print v print_trans_args args


let print_ruleset fmt args trans_name =
  if args = [] then begin
    fprintf fmt "@[<v 2>rule \"%s\"@ " trans_name;
    fun () -> fprintf fmt "@]@ end;@."
  end
  else begin
    fprintf fmt "@[<v 2>ruleset @[<hov>%a@] do rule \"%s\"@ "
      print_trans_args args trans_name;
    fun () -> fprintf fmt "@]@ end end;@."
  end


let print_transition fmt t =
  let args = t.tr_args in
  let close_ruleset = print_ruleset fmt args (Hstring.view t.tr_name) in
  print_guard fmt t;
  fprintf fmt "@]@.@[<v 2>==>@ ";
  fprintf fmt "%a%a%a"
    print_assigns t.tr_assigns
    print_updates t.tr_upds
    print_nondets t.tr_nondets;
  close_ruleset ()


let print_transitions fmt =
  List.iter (fun t -> fprintf fmt "%a\n" print_transition t.tr_info)


(********************************************)
(* Printing unsafe properties as invariants *)
(********************************************)

let print_invariant fmt name =
  fprintf fmt "@[<v 2>invariant \"%s\"@ " name;
  fun () -> fprintf fmt "@]@."


let rec distinct acc seen procs = match procs with
  | [] -> acc
  | p :: r ->
    let acc = List.fold_left (fun acc p' ->
        (p', p) :: acc
      ) acc seen in
    distinct acc (p :: seen) r
  
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
  

let print_unsafe =
  let cpt = ref 0 in
  fun fmt (procs, sa) ->
    let rprocs = List.map (fun p ->
        let p' = Bytes.of_string (Hstring.view p) in
        Bytes.set p' 0 'p';
        Hstring.make p'
      ) procs in
    let sigma = List.combine procs rprocs in
    let renamed_sa = SAtom.subst sigma sa in
    let close_invariant =
      print_invariant fmt ("not unsafe[" ^ string_of_int !cpt ^ "]") in
    incr cpt;
    let close_foralls = print_foralls fmt rprocs in
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

let print_system nbprocs abstr fmt sys =
  print_constants fmt nbprocs abstr; pp_print_newline fmt ();
  print_types fmt (); pp_print_newline fmt ();
  print_vars_defs fmt (sys.t_globals @ sys.t_arrays); pp_print_newline fmt ();
  print_inits fmt sys; pp_print_newline fmt ();
  print_transitions fmt sys.t_trans;
  print_unsafes fmt sys.t_unsafe
  
