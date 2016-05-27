open Ast
open Format
open Buffer
open Lexing
open Types
open Util


let print_consts_or_globals str fmt l =
  if l <> [] then
    let rec print fmt l =
      fprintf fmt "@[";
      match l with
        |[] -> fprintf fmt "@.@]"
        |(loc, name, t)::s ->
          if loc.active then
            fprintf fmt "%s %s : %s@.%a"
              str (Hstring.view name) (Hstring.view t) print s in
    print fmt l

let print_list_sep fmt (l, separator) =
 if l <> [] then
    let rec print fmt l =
      match l with
        |[] -> ()
        |x::[] ->  fprintf fmt "%s" (Hstring.view x)
        |x::s -> fprintf fmt "%s%s%a" (Hstring.view x) separator print s in
    print fmt l
      
let print_arrays fmt l = 
 if l <> [] then
    let rec print fmt l = 
      fprintf fmt "@[";
      match l with
        |[] -> fprintf fmt "@.@]"
        |(loc, name, (t_l, t))::s -> 
          if loc.active then 
            fprintf fmt "array %s [%a] : %s@.%a" 
              (Hstring.view name) print_list_sep (t_l, ",") (Hstring.view t) print s in
    print fmt l

let print_type_defs fmt l =
  if l <> [] then
    let rec print fmt l =
      fprintf fmt "@[";
      match l with
        |[] -> fprintf fmt "@.@]"
        |(loc, (name, t_l))::s ->
          if loc.active then
            fprintf fmt "type %s = %a@.%a"
              (Hstring.view name) print_list_sep (t_l, "|") print s in
    print fmt l


let print_dnf fmt l = 
 if l <> [] then
    let rec print fmt l = 
      match l with
        |[] -> ()
        |x::[] -> SAtom.print fmt x
        |x::s -> fprintf fmt "%a || %a" SAtom.print x print s in
    print fmt l


let print_init fmt i =
  let (loc,vl,dnf) = i in
  if loc.active then
    fprintf fmt "@[init (%a) { %a }@.@.@]" print_list_sep (vl, " ") print_dnf  dnf
    
let print_invs_or_unsafe str fmt l = 
  if l <> [] then
    let rec print fmt l = 
      match l with 
        |[] -> fprintf fmt "@.@.@]"
        |(loc,vl,satom)::s -> 
          if loc.active then 
            fprintf fmt "@[%s (%a) { %a }@.%a"
              str print_list_sep (vl, " ") SAtom.print satom print s 
    in 
    print fmt l

let rec print_ureq fmt l = 
  match l with 
    |[] -> ()
    |(v, dnf)::s -> 
      fprintf fmt " && forall_other %s. %a%a" 
        (Hstring.view v)  print_dnf dnf print_ureq  s

let print_swts fmt l = 
  let rec print fmt l =
    match l with
      |[] -> ()
      |(atom,t)::[] -> fprintf fmt "%a : %a"
        SAtom.print atom Term.print t
      |(atom,t)::s -> fprintf fmt " %a : %a @.| %a"
        SAtom.print atom Term.print t print s
  in 
  if l <> [] then (
    fprintf fmt "case @,|";
    print fmt l)
 
      
let rec print_glob_update fmt g =
  match g with
    |UTerm t -> Term.print fmt t
    |UCase (c) -> print_swts fmt (c) 
      
let print_assigns fmt l =
  if l <> [] then
    fprintf fmt "@[";
    let rec print fmt l =
      match l with
        |[] -> fprintf fmt "@]"
        |(name, glob,inf)::s -> 
          (if inf.active then 
            fprintf fmt "  %s := %a;@." 
              (Hstring.view name) print_glob_update glob);
          print fmt s
    in
    print fmt l


let print_upds fmt l =
  if l <> [] then
    let rec print fmt l =
      match l with
        |[] -> fprintf fmt "@]"
        |u::s -> 
          if u.up_loc.active then 
            (match u.up_info with 
              |None -> 
                fprintf fmt "  @[%s[%a] := %a;@.%a@]"
                  (Hstring.view u.up_arr) 
                  print_list_sep (u.up_arg,",") 
                  print_swts u.up_swts print s 
              |Some (name, var, t) -> 
                fprintf fmt "  @[%s[%a] := %a;@."
                  (Hstring.view name) 
                  print_list_sep (var,",") 
                  Term.print t);
          print fmt s
    in
    print fmt l

let print_nondets fmt l = 
  if l <> [] then 
    let rec print fmt l = 
      match l with 
        |[] -> ()
        |(v,_)::s -> fprintf fmt 
          "  @[%s%a := . ;@]@." (Hstring.view v)  print s in 
    print fmt l

let print_transitions fmt l = 
  if l <> [] then
    fprintf fmt "@[";
    let rec print fmt l = 
      match l with 
        |[] -> fprintf fmt "@]"
        |t::s -> 
          (if t.tr_loc.active then 
            fprintf fmt 
              "transition %s (%a)@.requires { @[%a%a@]}@.{@.@[%a%a%a@]}@.@." 
              (Hstring.view t.tr_name) print_list_sep (t.tr_args, " ")
              SAtom.print t.tr_reqs.r 
              print_ureq t.tr_ureq 
              print_nondets t.tr_nondets 
              print_assigns t.tr_assigns
              print_upds t.tr_upds);
          print fmt s in 
    print fmt l
    

let ast_to_string s = 
  let fmt = str_formatter in
  print_type_defs fmt s.type_defs ;
  print_consts_or_globals "var" fmt s.globals;
  print_consts_or_globals "const" fmt s.consts;
  print_arrays fmt s.arrays;
  print_init fmt s.init;
  print_invs_or_unsafe "invariant" fmt s.invs;
  print_invs_or_unsafe "unsafe" fmt s.unsafe;
  print_transitions fmt s.trans; 
  flush_str_formatter ()


let print_ast s fmt =
  print_type_defs fmt s.type_defs ;
  print_consts_or_globals "var" fmt s.globals;
  print_consts_or_globals "const" fmt s.consts;
  print_arrays fmt s.arrays;
  print_init fmt s.init;
  print_invs_or_unsafe "invariant" fmt s.invs;
  print_invs_or_unsafe "unsafe" fmt s.unsafe;
  print_transitions fmt s.trans
(* print_transitions s.trans; *)
     


