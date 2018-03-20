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

let pp_list_const fmt cl =
  Format.pp_print_list ~pp_sep:pp_sep_pipe Hstring.print fmt cl

let pp_list_pairs fmt cl =
  Format.pp_print_list ~pp_sep:pp_sep_pipe (
    fun fmc c -> Format.fprintf fmt "%a, %a" Hstring.print c Hstring.print c)
    fmt cl

let pp_term fmt = function
  | Elem (x, _) ->
    if Hstring.equal x mytrue then Format.fprintf fmt "true"
    else if Hstring.equal x myfalse then Format.fprintf fmt "false"
    else Format.fprintf fmt "%a" Hstring.print (uncapitalize x)
  | t -> Format.fprintf fmt "%s" (String.uncapitalize_ascii (
    Format.asprintf "%a" Term.print t))

let pp_atom fmt = function
  | Atom.Comp (t1, op, t2) -> Format.fprintf fmt "%a %a %a"
                                pp_term t1 print_op op pp_term t2
  | _ -> assert false


(* Transforms type declarations in scopes with definition of equality *)

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

let pp_trad_type_defs fmt tdl =
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
              Format.fprintf fmt "@,%a = %a;"
                pp_hstring_uncap id pp_term t2;
              acc
            | Access (id, _) ->
              Format.fprintf fmt "@,%a = Array.make n %a;"
                pp_hstring_uncap id pp_term t2;
              acc
            | _ -> assert false
          end;
        | Comp (t1, Neq, _) ->
          begin match t1 with
            | Elem (id, _) ->
              let acc = HSet.add id acc in
              Format.fprintf fmt "@,%a = -1;"
                pp_hstring_uncap id;
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

let print_satoms fmt sa =
  let pp_sep fmt () = Format.fprintf fmt " && @," in
  Format.fprintf fmt "@[<hov>%a@]"
    (Format.pp_print_list ~pp_sep:pp_sep pp_atom) (SAtom.elements sa)

let pp_guard map fmt g =
  print_satoms fmt g

let pp_uguard map fmt g = Format.fprintf fmt ""

module HMap = Hstring.HMap

let map_procs args pl =
  let rec aux acc = function
    | [], _ -> acc
    | hd1 :: tl1, hd2 :: tl2 -> aux (HMap.add hd1 hd2 acc) (tl1, tl2)
    | _ -> assert false
  in aux HMap.empty (args, pl)

let pp_transition ?cond:(cond="else if") pl fmt t =
  let map = map_procs t.tr_args pl in
  Format.fprintf fmt "(*%a*)@,\
                      @[<v 2>%s coin () && %a %a then begin@,\
                      (* updates *)\
                      @]@,end@,"
    Hstring.print t.tr_name cond
    (pp_guard map) t.tr_reqs (pp_uguard map) t.tr_ureq

let pp_transitions pl fmt s =
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
