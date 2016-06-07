open Lexing
open Util
open Types
open Ptree
open Format

let comments = ref true 

let print_hstr fmt  h =
  if h.hstr_i.active || not !comments then
    fprintf fmt "%s" (Hstring.view h.hstr)
  else 
    fprintf fmt "(*%s*)" (Hstring.view h.hstr)
      
let rec print_list_seph fmt (l, sep) = 
  match l with
    |[] -> ()
    |x::[] ->  fprintf fmt "%a" print_hstr x
    |x::s -> fprintf fmt "%a%s%a" print_hstr x sep print_list_seph (s,sep) 

let print_term fmt  = function
  | TVar (v, l) -> 
    if l.active || not !comments then Hstring.print fmt v.hstr 
    else fprintf fmt "(* %a *)" Hstring.print v.hstr
  | TTerm ((t, l),None) -> 
    if l.active || not !comments then Term.print fmt t 
    else fprintf fmt "(* %a *)" Term.print t
  | TTerm ((t, l), Some x) -> 
    if l.active || not !comments then
      fprintf fmt "%a [%a]" 
        print_hstr x.arr_n print_list_seph (x.arr_arg, ",")
    else
      fprintf fmt "(*%a [%a]*)" 
        print_hstr x.arr_n print_list_seph (x.arr_arg, ",")

let print_atom fmt  = function
  | AVar (v, l) -> 
    if l.active || not !comments then Hstring.print fmt v.hstr
    else (fprintf fmt "(* %a *)" Hstring.print v.hstr)
  | AAtom (a, l) -> 
    if l.active || not !comments then Atom.print fmt a 
    else fprintf fmt "(* %a *)" Atom.print a
  | AEq (t1, t2, l) -> 
    if l.active || not !comments then 
      fprintf fmt "(%a = %a)" print_term t1 print_term t2
    else (fprintf fmt "(* %a = %a *)" print_term t1 print_term t2)
  | ANeq (t1, t2, l) -> 
    if l.active || not !comments then
      fprintf fmt "(%a <> %a)" print_term t1 print_term t2
    else (fprintf fmt "(* %a <> %a *)" print_term t1 print_term t2)
  | ALe (t1, t2, l) -> 
    if l.active || not !comments then 
      fprintf fmt "(%a <= %a)" print_term t1 print_term t2
    else (fprintf fmt "(* %a <= %a *)" print_term t1 print_term t2 )
  | ALt (t1, t2, l) ->
    if l.active || not !comments then 
      fprintf fmt "(%a < %a)" print_term t1 print_term t2
    else (fprintf fmt "(* %a < %a *)" print_term t1 print_term t2 )

      
let get_active_atom = function
  | AVar (_, l) 
  | AAtom (_, l) -> l.active 
  | AEq (_, _, l) 
  | ANeq (_, _, l)  
  | ALe (_, _, l) 
  | ALt (_, _, l) -> l.active

let rec get_active_formula = function
  | PAtom (a) -> get_active_atom a
  | PNot (a,_,loc) -> loc.active
  | PAnd ([], loc) 
  | POr ([], loc) ->  loc.active
  | PAnd (l, loc)  
  | POr (l, loc) -> if loc.active then not (not_liste_active l) else loc.active
  | PImp (_, _, loc)  
  | PEquiv (_, _, loc) -> loc.active 
  | PIte (_, _, _, loc) -> loc.active 
  | PForall (_, _, loc)  
  | PExists (_, _, loc) 
  | PForall_other (_, _, loc) 
  | PExists_other (_, _, loc) -> loc.active
and not_liste_active l = 
  List.fold_left (fun acc x -> acc && (not (get_active_formula x))) true l 
    
let rec print_list_sep_form fmt (f, l, sep) =
  match l with
    |[] -> ()
    |x::[] -> fprintf fmt "%a" f x
    |x::y::[] ->
      if (get_active_formula x && get_active_formula y ) || not !comments then
        fprintf fmt "%a%s%a" f x sep  f y
      else if get_active_formula x then
        fprintf fmt "%a%a" f x f y
      else
        fprintf fmt "(*%a%s*)%a" f x sep f y
    |x::y::m ->
      let s = y::m  in
      if (get_active_formula x && get_active_formula y) || not !comments then
        fprintf fmt "%a%s%a" f x sep  print_list_sep_form (f, s, sep)
      else if get_active_formula x then
        fprintf fmt "%a%a" f x print_list_sep_form (f, s, sep)
      else
        if get_active_formula y then
          fprintf fmt "(*%a%s*)%s%a" f x sep sep print_list_sep_form (f, s, sep)
        else
          fprintf fmt "(*%a%s*)%a" f x sep print_list_sep_form (f, s, sep)       

let rec print_formula fmt f = 
  if get_active_formula f || not !comments then 
    print_f fmt f 
  else
    fprintf fmt "(* %a *)" print_f f
and
    print_f fmt  = function 
      | PAtom (a) -> print_atom fmt a 
      | PNot (not_i,f,loc) -> 
        if not_i.active || not !comments  then 
          fprintf fmt "( not (%a) )" print_formula f
        else 
          fprintf fmt "( (*not*) %a )" print_formula f
      | PAnd (l,loc) -> 
        fprintf fmt " %a " print_list_sep_form (print_formula, l, " && ")
      | POr (l,loc) ->
        fprintf fmt " %a " print_list_sep_form (print_formula, l, " || ")
      | PImp (a, b, loc) -> 
        fprintf fmt "( %a => %a )" print_formula a print_formula b
      | PEquiv (a, b, loc) ->
        fprintf fmt "( %a <=> %a )" print_formula a print_formula b
      | PIte (c, t, e, loc) -> 
        fprintf fmt " if (%a) then (%a) else (%a) "
          print_formula c print_formula t print_formula e
      | PForall (vs, f, loc) -> 
        (fprintf fmt " forall";
         List.iter (fun (x) -> fprintf fmt " %a " print_hstr x) vs;
         fprintf fmt "x. ( %a )" print_formula f)
      | PExists (vs, f, loc) -> 
        ( fprintf fmt " exists";
          List.iter (fun (x) -> fprintf fmt " %a " print_hstr x) vs;
          fprintf fmt ". ( %a )" print_formula f)
      | PForall_other (vs, f, loc) ->
        (fprintf fmt " forall_other";
         List.iter (fun (x) -> fprintf fmt " %a " print_hstr x) vs;
         fprintf fmt ". ( %a ) " print_formula f)
      | PExists_other (vs, f, loc) -> 
        (fprintf fmt " exists_other";
         List.iter (fun (x) -> fprintf fmt " %a " print_hstr x) vs;
         fprintf fmt ". ( %a )" print_formula f)
          


let rec print_list_sep fmt  (l, sep) =
  match l with
    |[] -> ()
    |x::[] -> fprintf fmt "%a" print_hstr x

    |x::s ->
      if x.hstr_i.active || not !comments  then
        fprintf fmt "%s%s%a" (Hstring.view x.hstr) sep print_list_sep (s,sep)
      else
        fprintf fmt "(*%s%s*)%a" (Hstring.view x.hstr) sep print_list_sep (s,sep)
          
let not_active l = 
  List.fold_left (fun acc x -> acc && (not x.hstr_i.active)) true l

let print_list_sep_type fmt  (l, sep) =
  let rec print fmt = function
    |[] -> ()
    |x::[] -> if x.hstr_i.active || not !comments then
        fprintf fmt "%s" (Hstring.view x.hstr) 
      else
        fprintf fmt "(*%s *)" (Hstring.view x.hstr) 
    |x::s ->
      if (x.hstr_i.active  && not_active s ) && !comments then
        fprintf fmt "%s%a" (Hstring.view x.hstr)  print s
      else if x.hstr_i.active || not !comments then
        fprintf fmt "%s%s%a"  (Hstring.view x.hstr) sep  print s
      else 
        fprintf fmt "(*%s%s*)%a" (Hstring.view x.hstr) sep  print s in
  print fmt l
    
    
let print_type_defs fmt l = 
  List.iter (fun (loc, (name, t_l)) ->
    let str_eq = 
      if List.length t_l = 0 then "" else " = " in 
    if loc.active || not !comments then
      fprintf fmt "type %s%s%a@." (Hstring.view name.hstr)
        str_eq print_list_sep_type (t_l, " | " ) 
    else
      fprintf fmt "(* type %s%s%a*)@." (Hstring.view name.hstr)
        str_eq print_list_sep_type (t_l, " | " )) l
    

let print_consts_or_globals fmt (str, l) = 
  List.iter (fun (loc, name, t) -> 
    if loc.active || not !comments then
      fprintf fmt "%s %s : %s@." str (Hstring.view name.hstr) (Hstring.view t.hstr)  
    else
      fprintf fmt "(* %s %s : %s*)@." str (Hstring.view name.hstr)
        (Hstring.view t.hstr)) l 
    

let print_arrays fmt  l = 
  List.iter (fun (loc, name, (t_l, t)) -> 
    if loc.active || not !comments then 
      fprintf fmt "array %a [%a] : %a@." 
        print_hstr name print_list_seph (t_l, ",")  print_hstr t
    else
      fprintf fmt "(* array %a [%a] : %a*)@." 
        print_hstr name print_list_seph (t_l, ",") print_hstr t) l

    
let print_init fmt  i =
  let (loc, vl, f) = i in
  if loc.active || not !comments then
    fprintf fmt "@[init (%a) { %a }@.@.@]" print_list_sep (vl, " ") print_formula f
  else
    fprintf fmt "(*@[init (%a) { %a }*)@.@.@]" print_list_sep (vl, " ") print_formula f


let print_invs_or_unsafe str fmt l = 
  List.iter (fun (loc, vl, f) -> 
    if loc.active || not !comments then 
      fprintf fmt "@[%s (%a) { %a }@.@.@]"
        str print_list_sep (vl, " ") print_formula f
    else 
      fprintf fmt "(* @[%s (%a) { %a }*)@.@.@]"
        str print_list_sep (vl, " ") print_formula f) l


let print_nondets fmt  l = 
  List.iter (fun x -> 
    if x.n_i.active || not !comments then 
      fprintf fmt "%s := . ;@;" (Hstring.view x.n_n.hstr)
    else
      fprintf fmt "(*%s := . ;*).@;" (Hstring.view x.n_n.hstr)
  ) l  

let print_swts fmt  l = 
  let rec print fmt = function
    |([]) -> ()
    |(x::[]) -> 
      if x.pup_i.active || not !comments then 
        fprintf fmt "| %a : %a@]" print_formula x.pup_form print_term x.pup_t
      else
        fprintf fmt " (* %a : %a*)@]" print_formula x.pup_form print_term x.pup_t
    |(x::s) -> 
      if x.pup_i.active || not !comments then 
        fprintf fmt "| %a : %a @;%a" print_formula x.pup_form print_term x.pup_t print s
      else 
        fprintf fmt "(* %a : %a *)@;%a" print_formula x.pup_form print_term 
          x.pup_t print s     in 
  if l <> [] then (
    fprintf fmt "@[<v 2>case @;";
    print fmt l)

let print_glob_update fmt = function
  |PUTerm (t,_) -> print_term fmt t
  |PUCase (c,_) -> print_swts fmt  (c) 


let print_assigns fmt l =
  List.iter (fun x ->
    if x.a_i.active || not !comments then
      fprintf fmt "%s := %a;@;" (Hstring.view x.a_n.hstr) print_glob_update x.a_p
    else
      fprintf fmt "(* %s := %a; *)@;" (Hstring.view x.a_n.hstr) 
        print_glob_update x.a_p)l
    
let print_upds fmt upds =
  List.iter (fun u -> 
    if u.pup_loc.active || not !comments then
      (match u.pup_info with 
        |None -> let (x,_) = u.pup_swts in 
                 let (p_arg,_) = u.pup_arg in 
                 fprintf fmt "%s[%a] := %a;@,"
                   (Hstring.view u.pup_arr.hstr) 
                   print_list_seph (p_arg,", ") print_swts x  
        |Some (name, var, t) -> fprintf fmt "%s[%a] := %a;@,"
          (Hstring.view name) print_list_seph (var,", ") print_term t)
    else
      (match u.pup_info with 
        |None -> 
          let (x,_) = u.pup_swts in 
          let (p_arg,_) = u.pup_arg in 
          fprintf fmt "(* %s[%a] := %a; *)@,"
            (Hstring.view u.pup_arr.hstr) print_list_seph (p_arg,", ") print_swts x  
        |Some (name, var, t) -> fprintf fmt "(* %s[%a] := %a; *)@,"
          (Hstring.view name) print_list_seph (var,", ") print_term t)) upds.t_pup_l
    

let print_ptrs fmt ptrs =
  if ptrs.ptr_i.active || not !comments then 
    fprintf fmt "@[<v>@,%a%a%a@]" 
      print_nondets ptrs.ptr_nondets 
      print_assigns ptrs.ptr_assigns
      print_upds ptrs.ptr_upds
  else
    fprintf fmt "@[<v>@,(*%a%a%a*)@]"
      print_nondets ptrs.ptr_nondets 
      print_assigns ptrs.ptr_assigns
      print_upds ptrs.ptr_upds
      
let print_transitions fmt  l = 
  List.iter (fun t ->
    if t.ptr_loc.active || not !comments then
      fprintf fmt "@[transition %a (%a)@.requires { @[%a@] }@.{%a@]@;}@.@."
        print_hstr t.ptr_name  print_list_sep (t.ptr_args, " ") 
        print_formula t.ptr_reqs.r_f print_ptrs t.ptr_s else 
      fprintf fmt "@[(* transition %a (%a)@.requires { @[%a@] }@.{%a} *)@.@.@]"
        print_hstr t.ptr_name  print_list_sep (t.ptr_args, " ")
        print_formula t.ptr_reqs.r_f print_ptrs t.ptr_s
  ) l
    
let print_psystem psys  fmt = 
  print_type_defs fmt psys.ptype_defs;
  print_consts_or_globals fmt ("var", psys.pglobals);
  print_consts_or_globals fmt ("const", psys.pconsts);
  print_arrays fmt psys.parrays;
  print_init fmt psys.pinit;
  print_invs_or_unsafe "invs" fmt  psys.pinvs;
  print_invs_or_unsafe "unsafe" fmt  psys.punsafe;
  print_transitions fmt  (List.rev psys.ptrans)

let psystem_to_string psys   =
  let fmt = str_formatter in 
  print_psystem psys fmt;
  flush_str_formatter ()
    

    
