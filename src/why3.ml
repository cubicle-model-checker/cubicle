open Ast
open Types

let tbool = Hstring.make "mbool"

let mytrue = Hstring.make "@MTrue"
let myfalse = Hstring.make "@MFalse"

let capitalize h =
  Hstring.make @@ String.capitalize_ascii @@ Hstring.view h

let uncapitalize h =
  Hstring.make @@ String.uncapitalize_ascii @@ Hstring.view h

let pp_hstring_cap fmt h = Hstring.print fmt @@ capitalize h

let pp_hstring_uncap fmt h = Hstring.print fmt @@ uncapitalize h

let pp_cut_if_nempty l =
  if List.compare_length_with l 0 > 0 then Format.print_cut ()

let pp_sep_pipe fmt () = Format.fprintf fmt " |@ "

let pp_sep_and_ml fmt () = Format.fprintf fmt " && @ "
let pp_sep_and_log fmt () = Format.fprintf fmt " /\\ @ "

let pp_sep_nil fmt () = Format.fprintf fmt ""

let pp_for fmt u =
  Format.fprintf fmt "for %a = 0 to s.%a.length - 1 do"
    Variable.print_vars u.up_arg pp_hstring_uncap u.up_arr

let pp_list_const fmt cl =
  Format.pp_print_list ~pp_sep:pp_sep_pipe Hstring.print fmt cl

let pp_list_pairs fmt cl =
  Format.pp_print_list ~pp_sep:pp_sep_pipe (
    fun fmc c -> Format.fprintf fmt "%a, %a" Hstring.print c Hstring.print c)
    fmt cl

let pp_term ?(syst=false) sub fmt t =
  if syst then
    (match t with
      | Elem (_, Glob) | Elem (_, Var) | Access _ -> Format.fprintf fmt "s."
      | _ -> ());
  match t with
    | Elem (x, s) ->
      if Hstring.equal x mytrue then Format.fprintf fmt "true"
      else if Hstring.equal x myfalse then Format.fprintf fmt "false"
      else Format.fprintf fmt "%a" Hstring.print (
        match s with
          | Constr -> x
          | Glob -> uncapitalize x
          | Var -> Variable.subst sub x
      )
    | Access (id, vl) ->
      let vl = List.map (Variable.subst sub) vl in
      Format.fprintf fmt "%a[%a]" pp_hstring_uncap id Variable.print_vars vl
    | t -> Format.fprintf fmt "%a" Term.print t

let pp_term_syst = pp_term ~syst:true

let pp_atom sub fmt = function
  | Atom.Comp (t1, op, t2) ->
    Format.fprintf fmt "%a %a %a"
      (pp_term sub) t1 print_op op (pp_term sub) t2
  | a -> Format.fprintf fmt "%a" Atom.print a

let pp_satoms ?(pp_sep=pp_sep_and_ml) sub fmt sa =
  Format.fprintf fmt "@[<hov>%a@]"
    (Format.pp_print_list ~pp_sep (pp_atom sub)) (SAtom.elements sa)

(* Transforms type declarations in scopes with definition of equality *)

let pp_trad_type_defs fmt tdl =
  let pp_trad_type_def fmt (_, (t, cl)) =
    if not @@ Hstring.equal t tbool then
      Format.fprintf fmt "@[<v 2>scope import %a@,\
                          @,\
                          type %a = @[<hov 2>%a@]@,\
                          @,\
                          @[<v 2>let (=) (a b: %a): bool@,\
                          ensures {result <-> a = b}@,\
                          = @[<v 0>match a, b with@,\
                          | @[<hov>%a@] -> true@,\
                          | _ -> false\
                          @]@]@ end@,@]@,\
                          end@,\
                         "
        pp_hstring_cap t
        Hstring.print t
        pp_list_const cl
        Hstring.print t
        pp_list_pairs cl
  in
  Format.pp_print_list pp_trad_type_def fmt tdl

let pp_type fmt t =
  if Hstring.equal t tbool then Format.fprintf fmt "bool"
  else Format.fprintf fmt "%a" Hstring.print t

let pp_global_to_field fmt (_, id, ty) =
  Format.fprintf fmt "@[mutable %a : %a;@]" pp_hstring_uncap id pp_type ty

let pp_array_to_field fmt (_, id, (ktl, ty)) =
  assert (List.compare_length_with ktl 1 = 0);
  Format.fprintf fmt "@[%a : array %a;@]" pp_hstring_uncap id pp_type ty

let pp_system_to_type fmt s =
  Format.pp_print_list pp_global_to_field fmt s.globals;
  pp_cut_if_nempty s.arrays;
  Format.pp_print_list pp_array_to_field fmt s.arrays

module HSet = Hstring.HSet

let pp_init fmt {globals; init = (_, _, dnf)} =
  let open Atom in
  let elems = List.fold_left (fun acc (_, id, _) -> HSet.add id acc)
      HSet.empty globals in
  let init_elems = List.fold_left (fun acc sa ->
    SAtom.fold (fun a acc ->
      match a with
        | Comp (t1, Eq, t2) ->
          begin match t1 with
            | Elem (id, _) ->
              let acc = HSet.add id acc in
              Format.fprintf fmt "@,%a = %a;" pp_hstring_uncap id (pp_term []) t2;
              acc
            | Access (id, _) ->
              Format.fprintf fmt "@,%a = Array.make n %a;"
                pp_hstring_uncap id (pp_term []) t2;
              acc
            | _ -> assert false
          end;
        | Comp (t1, Neq, _) ->
          begin match t1 with
            | Elem (id, _) ->
              let acc = HSet.add id acc in
              Format.fprintf fmt "@,%a = -1;" pp_hstring_uncap id;
              acc
            | Access (id, _) ->
              Format.fprintf fmt "@,%a = Array.make n -1;"
                pp_hstring_uncap id;
              acc
            | _ -> assert false
          end
        | _ -> assert false
    ) sa acc
  ) HSet.empty dnf in
  let ninit_elems = HSet.diff elems init_elems in
  HSet.iter (fun e ->
    Format.fprintf fmt "@,%a = Random.random_int n"
      pp_hstring_uncap e
  ) ninit_elems

let init n f =
  let rec aux i acc =
    if i = n then List.rev acc
    else aux (i+1) (f i :: acc)
  in aux 0 []

let new_procs a =
  init a (fun i -> Hstring.make @@ Printf.sprintf "p%d" i)

let pp_newprocs fmt l =
  List.iter (
    Format.fprintf fmt "let %a = Random.random_int n in@," Hstring.print) l;
  Format.fprintf fmt "(*If there is more than one value,@,\
                      the variables could be equal, need to work on it*)"

let pp_guard sub fmt g =
  pp_satoms sub fmt g

let pp_uguard map fmt g =
  if g <> [] then Format.fprintf fmt "(* todo forall_other *)"
  else Format.fprintf fmt ""

let map_procs args pl =
  let rec aux acc = function
    | [], _ -> acc
    | hd1 :: tl1, hd2 :: tl2 -> aux ((hd1, hd2) :: acc) (tl1, tl2)
    | _ -> assert false
  in aux [] (args, pl)

let pp_arr_access sub fmt u =
  let vl = List.map (Variable.subst sub) u.up_arg in
  Format.fprintf fmt "%a[%a]" pp_hstring_uncap u.up_arr Variable.print_vars vl

let pp_assigns sub fmt al =
  let pp_upd fmt = function
    | UTerm t -> Format.fprintf fmt "%a" (pp_term_syst sub) t
    | _ -> Format.eprintf "pp_assigns@."; assert false
  in
  let pp_assign fmt (id, upd) =
    Format.fprintf fmt "s.%a <- %a;@," pp_hstring_uncap id pp_upd upd
  in
  Format.fprintf fmt "@[<v 0>%a@]"
    (Format.pp_print_list ~pp_sep:pp_sep_nil pp_assign) al

let is_true sa = SAtom.equal sa (SAtom.singleton Atom.True)

let pp_updates sub fmt ul =
  let pp_swt fmt (sa, t) =
    if is_true sa then
      Format.fprintf fmt "else (*%a*) %a" (pp_satoms sub ) sa (pp_term_syst sub) t
    else Format.fprintf fmt "if %a then %a" (pp_satoms sub) sa (pp_term_syst sub) t
  in
  let pp_swts fmt swts =
    Format.fprintf fmt "@[<v 0>%a@]" (Format.pp_print_list pp_swt) swts
  in
  let pp_prev fmt prev =
    Format.fprintf fmt "@[<v 0>%a@]"
      (Format.pp_print_list ~pp_sep:pp_sep_and_log
         (pp_satoms ~pp_sep:pp_sep_and_log sub)) prev
  in
  let pp_invariant ?(last=false) prev u fmt (inv, t) =
    if last then Format.fprintf fmt "(%a" pp_prev prev
    else
      Format.fprintf fmt "(%a%s%a"
        (pp_satoms ~pp_sep:pp_sep_and_log sub) inv
        (if prev <> [] then " /\\ " else "") pp_prev prev;
    let sub = Variable.build_subst u.up_arg [Hstring.make "p"] @ sub in
    Format.fprintf fmt " -> s.%a = %a)" (pp_arr_access sub) u (pp_term sub) t
  in
  let pp_invariants fmt u =
    Format.fprintf fmt "invariant { @[<v 2>forall p:proc. 0 <= p < %a ->@,"
      Variable.print_vars u.up_arg;
    let rec aux prev fmt = function
      | [upd] -> pp_invariant ~last:true prev u fmt upd
      | ((inv, _) as upd) :: tl -> pp_invariant prev u fmt upd;
        Format.fprintf fmt " /\\@,";
        aux (SAtom.map Atom.neg inv :: prev) fmt tl
      | _ -> assert false
    in
    aux [] fmt u.up_swts;
    Format.fprintf fmt " }@]@,@,"
  in
  let pp_upd fmt u =
    Format.fprintf fmt "@[<v 2>%a@,%as.%a <- %a@]@,done;"
      pp_for u pp_invariants u (pp_arr_access sub) u pp_swts u.up_swts
  in
  Format.fprintf fmt "@[<v 0>%a@]" (Format.pp_print_list pp_upd) ul

let pp_transitions pl fmt s =
  let pp_transition ?(cond="else if") pl fmt t =
    let map = map_procs t.tr_args pl in
    Format.fprintf fmt "(*%a*)@,\
                        @[<hov 2>%s coin () &&@ %a@ %a@]@ \
                        @[<v 2>then begin@,label %a in@,%a%a@]@,end@,"
      Hstring.print t.tr_name cond
      (pp_guard map) t.tr_reqs (pp_uguard map) t.tr_ureq
      pp_hstring_cap t.tr_name
      (pp_assigns map) t.tr_assigns (pp_updates map) t.tr_upds
      (* (pp_nondets map) t.tr_nondets *)
  in
  match s.trans with
    | hd :: tl ->
      Format.fprintf fmt "%a@," (pp_transition ~cond:"if" pl) hd;
      Format.pp_print_list (pp_transition pl) fmt tl
    | _ -> assert false

(* Transforms a Cubicle program in a whyml one *)

let cub_to_whyml s fmt file =
  let name = Filename.(remove_extension @@ basename file) in
  Format.fprintf fmt "@[<v>\
                      module %s@,\
                      @,\
                      use import array.Array@,\
                      use import int.Int@,\
                      use import ref.Refint@,\
                      use import random.Random@,\
                     " (String.capitalize_ascii name);
  Format.fprintf fmt "%a" pp_trad_type_defs s.type_defs;
  Format.fprintf fmt "@,val coin () : bool@,";
  Format.fprintf fmt "@,type proc = int@,";

  Format.fprintf fmt "@,@[<v 2>type system = {@,%a@]@,}"
    pp_system_to_type s;
  Format.fprintf fmt "@,@[<v 2>let %s (n : int) : system@,\
                      diverges@,\
                      requires { 0 < n }@]@,\
                      @[<v 2>=@,"
    name;
  Format.fprintf fmt "@[<v 2>let s = {%a@]@,} in" pp_init s;
  Format.fprintf fmt "@,@[<v 2>while true do@,";
  let plist = new_procs s.max_arity in
  Format.fprintf fmt "@,%a@," pp_newprocs plist;
  Format.fprintf fmt "@,%a@," (pp_transitions plist) s;
  Format.fprintf fmt "@]@,done;@,s@]@,end";
  Format.fprintf fmt "@.";
  exit 0
