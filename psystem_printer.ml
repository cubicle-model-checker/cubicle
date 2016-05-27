open Lexing
open Util
open Types
open Ptree
open Format

let print_term fmt = function
  | TVar (v, _) -> fprintf fmt "%a" Hstring.print v
  | TTerm (t, _) -> Term.print fmt t

let print_atom fmt = function
  | AVar (v, _) -> fprintf fmt "%a" Hstring.print v
  | AAtom (a, _) -> Atom.print fmt a
  | AEq (t1, t2, _) -> fprintf fmt "%a = %a" print_term t1 print_term t2
  | ANeq (t1, t2, _) -> fprintf fmt "%a <> %a" print_term t1 print_term t2
  | ALe (t1, t2, _) -> fprintf fmt "%a <= %a" print_term t1 print_term t2
  | ALt (t1, t2, _) -> fprintf fmt "%a < %a" print_term t1 print_term t2

let rec print_list_sep_f fmt (f, l, sep) = 
  match l with
    |[] -> ()
    |(x)::[] ->  fprintf fmt "%a" f x
    |(x)::s -> fprintf fmt "%a%s%a" f x sep print_list_sep_f (f, s, sep) 

let rec print_formula fmt  = function 
  | PAtom (a) -> print_atom fmt a
  | PNot (f,_) -> fprintf fmt "( not %a )" print_formula f
  | PAnd (l,_) -> fprintf fmt "( %a )" print_list_sep_f (print_formula, l, " && ")
  | POr (l,_) -> fprintf fmt "( %a )" print_list_sep_f (print_formula, l, " || ")
  | PImp (a, b, _) -> fprintf fmt "( %a => %a )" print_formula a print_formula b
  | PEquiv (a, b, _) -> fprintf fmt "( %a <=> %a )" print_formula a print_formula b
  | PIte (c, t, e, _) ->
    fprintf fmt "( if %a then %a else %a )" print_formula c print_formula t
      print_formula e
  | PForall (vs, f, _) ->
    fprintf fmt "( forall";
    List.iter (fprintf fmt " %a" Variable.print) vs;
    fprintf fmt ". %a )" print_formula f
  | PExists (vs, f, _) ->
    fprintf fmt "( exists";
    List.iter (fprintf fmt " %a" Variable.print) vs;
    fprintf fmt ". %a )" print_formula f
  | PForall_other (vs, f, _) ->
    fprintf fmt "( forall_other";
    List.iter (fprintf fmt " %a" Variable.print) vs;
    fprintf fmt ". %a )" print_formula f
  | PExists_other (vs, f, _) ->
    fprintf fmt "( exists_other";
    List.iter (fprintf fmt " %a" Variable.print) vs;
    fprintf fmt ". %a )" print_formula f

let rec print_list_sep fmt (l, sep) = 
  match l with
    |[] -> ()
    |x::[] ->  fprintf fmt "%s" (Hstring.view x)
    |x::s -> fprintf fmt "%s%s%a" (Hstring.view x) sep print_list_sep (s,sep) 

  
let print_type_defs fmt l = 
    List.iter (fun (loc, (name, t_l)) -> 
      if loc.active then
        fprintf fmt "type %s = %a@." (Hstring.view name) print_list_sep (t_l, " | " )) l
          

let print_consts_or_globals str fmt l = 
    List.iter (fun (loc, name, t) -> 
      if loc.active then
        fprintf fmt "%s %s : %s@." str (Hstring.view name) (Hstring.view t)) l 


let print_arrays fmt l = 
   List.iter (fun (loc, name, (t_l, t)) -> 
     if loc.active then 
       fprintf fmt "array %s [%a] : %s@." 
         (Hstring.view name) print_list_sep (t_l, ",") (Hstring.view t)) l

   
let print_init fmt i =
  let (loc, vl, f) = i in
  if loc.active then
    fprintf fmt "@[init (%a) { %a }@.@.@]" print_list_sep (vl, " ") print_formula f


let print_invs_or_unsafe str fmt l = 
  List.iter (fun (loc, vl, f) -> 
     if loc.active then 
       fprintf fmt "@[%s (%a) { %a }@.@]" 
         str print_list_sep (vl, " ") print_formula f) l


let print_nondets fmt l = 
  List.iter (fun x -> 
    fprintf fmt "  @[%s := . ;@]@." (Hstring.view x.n_n)) l  

let print_swts fmt l = 
  let rec print fmt = function
      |[] -> ()
      |(f, t)::[] -> fprintf fmt "%a : %a" print_formula f print_term t
      |(f, t)::s -> fprintf fmt " %a : %a | %a" print_formula f print_term t print s
  in 
  if l <> [] then (
    fprintf fmt "case @,|";
    print fmt l)

let print_glob_update fmt = function
    |PUTerm t -> print_term fmt t
    |PUCase (c) -> print_swts fmt (c) 
      
let print_assigns fmt l =
  List.iter (fun x -> 
    if x.a_i.active then 
      fprintf fmt "@[%s := %a;@.@]" (Hstring.view x.a_n) print_glob_update x.a_p) l
    
let print_upds fmt l =
  List.iter ( fun u ->  
    if u.pup_loc.active then 
      (match u.pup_info with 
        |None -> fprintf fmt "  @[%s[%a] := %a;@.@]"
          (Hstring.view u.pup_arr) print_list_sep (u.pup_arg," ") print_swts u.pup_swts  
        |Some (name, var, t) -> fprintf fmt "  @[%s[%a] := %a;@."
          (Hstring.view name) print_list_sep (var," ") print_term t)) l
    
let print_transitions fmt l = 
  List.iter (fun t ->
    if t.ptr_loc.active then
      fprintf fmt "transition %s (%a)@.requires { @[%a@] }@.{@.@[%a%a%a@]}@.@."
        (Hstring.view t.ptr_name)  print_list_sep (t.ptr_args, " ")
        print_formula t.ptr_reqs.r_f print_nondets t.ptr_nondets print_assigns t.ptr_assigns
        print_upds t.ptr_upds) l
         
let print_psystem psys fmt = ()
  (* print_type_defs fmt psys.ptype_defs; *)
  (* print_consts_or_globals "var" fmt psys.pglobals; *)
  (* print_consts_or_globals "const" fmt psys.pconsts; *)
  (* print_arrays fmt psys.parrays; *)
  (* print_init fmt psys.pinit; *)
  (* print_invs_or_unsafe "invs" fmt psys.pinvs; *)
  (* print_invs_or_unsafe "unsafe" fmt psys.punsafe; *)
  (* print_transitions fmt (List.rev psys.ptrans) *)

let psystem_to_string psys =
  let fmt = str_formatter in 
  print_psystem psys fmt;
  flush_str_formatter ()
     

     
