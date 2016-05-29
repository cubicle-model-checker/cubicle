open Lexing
open Util
open Types
open Ptree
open Format


let print_term fmt = function
  | TVar (v, l) -> 
    if l.active then Hstring.print fmt v else fprintf fmt "(* %a *)" Hstring.print v
  | TTerm (t, l) -> 
    if l.active then Term.print fmt t else fprintf fmt "(* %a *)" Term.print t

let print_atom fmt = function
  | AVar (v, l) -> 
    if l.active then Hstring.print fmt v else 
      (fprintf fmt "(* %a *)" Hstring.print v)
  | AAtom (a, l) -> 
    if l.active then Atom.print fmt a else fprintf fmt "(* %a *)" Atom.print a
  | AEq (t1, t2, l) -> 
    if l.active then fprintf fmt "%a = %a" print_term t1 print_term t2
    else (fprintf fmt "(* %a = %a *)" print_term t1 print_term t2)
  | ANeq (t1, t2, l) -> 
    if l.active then fprintf fmt "%a <> %a" print_term t1 print_term t2
    else (fprintf fmt "(* %a <> %a *)" print_term t1 print_term t2)
  | ALe (t1, t2, l) -> 
    if l.active then fprintf fmt "%a <= %a" print_term t1 print_term t2
    else (fprintf fmt "(* %a <= %a *)" print_term t1 print_term t2 )
  | ALt (t1, t2, l) ->
    if l.active then fprintf fmt "%a < %a" print_term t1 print_term t2
    else (fprintf fmt "(* %a < %a *)" print_term t1 print_term t2 )

  
let get_active_atom = function
  | AVar (_, l) 
  | AAtom (_, l) -> l.active 
  | AEq (_, _, l) 
  | ANeq (_, _, l)  
  | ALe (_, _, l) 
  | ALt (_, _, l) -> l.active

let get_active_formula = function
  | PAtom (a) -> get_active_atom a
  | PNot (_,loc)  
  | PAnd (_,loc)  
  | POr (_,loc) -> loc.active 
  | PImp (_, _, loc)  
  | PEquiv (_, _, loc) -> loc.active 
  | PIte (_, _, _, loc) -> loc.active 
  | PForall (_, _, loc)  
  | PExists (_, _, loc) 
  | PForall_other (_, _, loc) 
  | PExists_other (_, _, loc) -> loc.active

let rec print_list_sep_f fmt (f, l, sep) = 
    match l with
    |[] -> ()
    |x::[] -> fprintf fmt "%a" f x
    |x::s -> 
      let y::ss = s in
      if get_active_formula x && get_active_formula y then  
        fprintf fmt "%a%s%a" f x sep print_list_sep_f (f, s, sep)
      else  
        fprintf fmt "%a%a" f x  print_list_sep_f (f, s, sep)
      


let rec print_formula fmt  = function 
  | PAtom (a) -> if get_active_atom a then print_atom fmt a 
    else (fprintf fmt "(* %a *)" print_atom a )
  | PNot (f,loc) -> if loc.active then fprintf fmt " not %a " print_formula f
    else (fprintf fmt "(* not %a *)" print_formula f )
  | PAnd (l,loc) -> if loc.active then 
      fprintf fmt " %a " print_list_sep_f (print_formula, l, " && ")
    else (fprintf fmt "(* %a *)" print_list_sep_f (print_formula, l, " && ") )
  | POr (l,loc) -> if loc.active then 
      fprintf fmt " %a " print_list_sep_f (print_formula, l, " || ")
    else (fprintf fmt "(* %a *)" print_list_sep_f (print_formula, l, " || ") )
  | PImp (a, b, loc) -> if loc.active then
      fprintf fmt " %a => %a " print_formula a print_formula b
    else (fprintf fmt "(* %a => %a *)" print_formula a print_formula b )
  | PEquiv (a, b, loc) -> if loc.active then 
      fprintf fmt " %a <=> %a " print_formula a print_formula b
    else (fprintf fmt "(* %a <=> %a *)" print_formula a print_formula b )
  | PIte (c, t, e, loc) -> if loc.active then 
    fprintf fmt " if %a then %a else %a " print_formula c print_formula t print_formula e
    else (fprintf fmt "(* if %a then %a else %a *)" print_formula c print_formula t print_formula e)
  | PForall (vs, f, loc) -> if loc.active then 
      (fprintf fmt " forall";
       List.iter (fun (x) -> fprintf fmt " %a" Variable.print x) vs;
       fprintf fmt "x. %a " print_formula f)
      else 
      (fprintf fmt "(* forall";
       List.iter (fun (x) -> fprintf fmt " %a" Variable.print x) vs;
       fprintf fmt ". %a *)" print_formula f)
  | PExists (vs, f, loc) -> if loc.active then
   ( fprintf fmt " exists";
    List.iter (fun (x) -> fprintf fmt " %a" Variable.print x) vs;
    fprintf fmt ". %a " print_formula f)
    else 
      (fprintf fmt "(* exists";
       List.iter (fun (x) -> fprintf fmt " %a" Variable.print x) vs;
       fprintf fmt ". %a *)" print_formula f)
  | PForall_other (vs, f, loc) -> if loc.active then 
    (fprintf fmt " forall_other";
    List.iter (fun (x) -> fprintf fmt " %a" Variable.print x) vs;
    fprintf fmt ". %a " print_formula f)
    else
      (fprintf fmt "(* forall_other";
       List.iter (fun (x) -> fprintf fmt " %a" Variable.print x) vs;
       fprintf fmt ". %a *)" print_formula f)
  | PExists_other (vs, f, loc) -> if loc.active then 
      (fprintf fmt " exists_other";
       List.iter (fun (x) -> fprintf fmt " %a" Variable.print x) vs;
       fprintf fmt ". %a " print_formula f)
    else 
      (fprintf fmt "(* exists_other";
       List.iter (fun (x) -> fprintf fmt " %a" Variable.print x) vs;
       fprintf fmt ". %a *)" print_formula f)


let rec print_list_sep fmt (l, sep) = 
  match l with
    |[] -> ()
    |x::[] ->  fprintf fmt "%s" (Hstring.view x)
    |x::s -> fprintf fmt "%s%s%a" (Hstring.view x) sep print_list_sep (s,sep) 

  
let print_type_defs fmt l = 
    List.iter (fun (loc, (name, t_l)) -> 
      if loc.active then
        fprintf fmt "type %s = %a@." (Hstring.view name) print_list_sep (t_l, " | " ) 
      else
        fprintf fmt "(* type %s = %a*)@." (Hstring.view name) print_list_sep (t_l, " | " )) l
     

let print_consts_or_globals str fmt l = 
    List.iter (fun (loc, name, t) -> 
      if loc.active then
        fprintf fmt "%s %s : %s@." str (Hstring.view name) (Hstring.view t)  
        else
        fprintf fmt "(* %s %s : %s*)@." str (Hstring.view name) (Hstring.view t)) l 
       

let print_arrays fmt l = 
   List.iter (fun (loc, name, (t_l, t)) -> 
     if loc.active then 
         fprintf fmt "array %s [%a] : %s@." 
           (Hstring.view name) print_list_sep (t_l, ",") (Hstring.view t) 
      else
         fprintf fmt "(* array %s [%a] : %s*)@." 
           (Hstring.view name) print_list_sep (t_l, ",") (Hstring.view t)) l

   
let print_init fmt i =
  let (loc, vl, f) = i in
  if loc.active then
    fprintf fmt "@[init (%a) { %a }@.@.@]" print_list_sep (vl, " ") print_formula f
  else
    fprintf fmt "(*@[init (%a) { %a }@.@.@]*)" print_list_sep (vl, " ") print_formula f


let print_invs_or_unsafe str fmt l = 
  List.iter (fun (loc, vl, f) -> 
     if loc.active then 
       fprintf fmt "@[%s (%a) { %a }@.@]"
         str print_list_sep (vl, " ") print_formula f
    else 
       fprintf fmt "(* @[%s (%a) { %a }@.@] *)"
         str print_list_sep (vl, " ") print_formula f) l


let print_nondets fmt l = 
  List.iter (fun x -> 
    fprintf fmt "  @[%s := . ;@]@." (Hstring.view x.n_n)) l  

let print_swts fmt l = 
  let rec print fmt = function
      |([]) -> ()
      |((f, t, i)::[]) -> 
        if i.active then 
          fprintf fmt "%a : %a" print_formula f print_term t
        else
          fprintf fmt "(*%a : %a*)" print_formula f print_term t
    |((f, t, i)::s) -> 
      if i.active then 
        fprintf fmt " %a : %a | %a" print_formula f print_term t print s
      else 
        fprintf fmt "(* %a : %a | %a*)" print_formula f print_term t print s
     
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
      fprintf fmt "@[%s := %a;@.@]" (Hstring.view x.a_n) print_glob_update x.a_p
    else
      fprintf fmt "@[(* %s := %a; *)@.@]" (Hstring.view x.a_n) print_glob_update x.a_p)l
    
let print_upds fmt l =
  List.iter (fun u ->  
    Printf.printf "%b\n" u.pup_loc.active;
    if u.pup_loc.active then 
      (match u.pup_info with 
      |None -> fprintf fmt "  @[%s[%a] := %a;@.@]"
        (Hstring.view u.pup_arr) print_list_sep (u.pup_arg," ") print_swts u.pup_swts  
      |Some (name, var, t) -> fprintf fmt "  @[%s[%a] := %a;@]@."
        (Hstring.view name) print_list_sep (var," ") print_term t)
    else
      (match u.pup_info with 
      |None -> fprintf fmt "  @[(* %s[%a] := %a; *)@.@]"
        (Hstring.view u.pup_arr) print_list_sep (u.pup_arg," ") print_swts u.pup_swts  
      |Some (name, var, t) -> fprintf fmt "  @[(* %s[%a] := %a; *)@.@]"
        (Hstring.view name) print_list_sep (var," ") print_term t)) l
    
let print_transitions fmt l = 
  List.iter (fun t ->
    if t.ptr_loc.active then
      fprintf fmt "transition %s (%a)@.requires { @[%a@] }@.{@.@[%a%a%a@]}@.@."
        (Hstring.view t.ptr_name)  print_list_sep (t.ptr_args, " ")
        print_formula t.ptr_reqs.r_f print_nondets t.ptr_s.ptr_nondets 
        print_assigns t.ptr_s.ptr_assigns  print_upds t.ptr_s.ptr_upds.p
    else 
      fprintf fmt "(* transition %s (%a)@.requires { @[%a@] }@.{@.@[%a%a%a@]} *)@.@."
        (Hstring.view t.ptr_name)  print_list_sep (t.ptr_args, " ")
        print_formula t.ptr_reqs.r_f print_nondets t.ptr_s.ptr_nondets 
        print_assigns t.ptr_s.ptr_assigns print_upds t.ptr_s.ptr_upds.p
     ) l
         
let print_psystem psys fmt = 
  print_type_defs fmt psys.ptype_defs;
  print_consts_or_globals "var" fmt psys.pglobals;
  print_consts_or_globals "const" fmt psys.pconsts;
  print_arrays fmt psys.parrays;
  print_init fmt psys.pinit;
  print_invs_or_unsafe "invs" fmt psys.pinvs;
  print_invs_or_unsafe "unsafe" fmt psys.punsafe;
  print_transitions fmt (List.rev psys.ptrans)

let psystem_to_string psys =
  let fmt = str_formatter in 
  print_psystem psys fmt;
  flush_str_formatter ()
     

     
