open Ast
open Format
open Buffer
open Lexing
open Types


let print_consts_or_globals l =
  if l <> [] then
    let rec print l = 
      fprintf str_formatter "@[<v>";
      match l with
        |[] -> fprintf str_formatter "@.@]"
        |(_, name, t)::s -> fprintf str_formatter "var %s : %s@." 
          (Hstring.view name) (Hstring.view t); print s in
    print l

let print_liste_sep l separator= 
 if l <> [] then
    let rec print l = 
      match l with
        |[] -> ()
        |x::[] ->  fprintf str_formatter "%s" (Hstring.view x)
        |x::s -> fprintf str_formatter "%s %s " (Hstring.view x) separator; print s in
    print l
  
      
let print_arrays l = 
 if l <> [] then
    let rec print l = 
      fprintf str_formatter "@[<v>";
      match l with
        |[] -> fprintf str_formatter "@.@]"
        |(_, name, (t_l, t))::s -> 
          fprintf str_formatter "%s %s [" "array"(Hstring.view name) ;
          print_liste_sep t_l ";";
          fprintf str_formatter "] : %s@." (Hstring.view t) ;         
          print s in
    print l

let print_type_defs l = 
  if l <> [] then
    let rec print l = 
      fprintf str_formatter "@[<v>";
      match l with
        |[] -> fprintf str_formatter "@.@]"
        |(_, (name, t_l))::s -> 
          fprintf str_formatter "type %s : " (Hstring.view name);
          print_liste_sep t_l "|";
          fprintf str_formatter "@.";
          print s in
    print l


let print_dnf l = 
 if l <> [] then
    let rec print l = 
      match l with
        |[] -> ()
        |x::[] -> SAtom.print str_formatter x
        |x::s -> 
          SAtom.print str_formatter x ; 
          fprintf str_formatter "|| " ;
          print s in
    print l
  

(* init : info * Variable.t list * dnf; *)
let print_init i = 
  let (_,vl,dnf) = i in 
  fprintf str_formatter "@[<v>init (" ;
  print_liste_sep vl ",";
  fprintf str_formatter ") { ";
  print_dnf dnf;
  fprintf str_formatter " }@.@]"

let print_invs l = 
  if l <> [] then
    let rec print l = 
      match l with 
        |[] -> fprintf str_formatter "@.@]"
        |(_,vl,satom)::s -> 
          fprintf str_formatter "@[<v>invariant (" ;
          print_liste_sep vl ",";
          fprintf str_formatter ") { ";
          SAtom.print str_formatter satom;
          fprintf str_formatter " }@." ;
          print s in 
    print l




let print_ast s = 
  print_type_defs s.type_defs;
  print_consts_or_globals s.globals;
  print_consts_or_globals s.consts;
  print_arrays s.arrays;
  print_init s.init;
  print_invs s.invs;
  flush_str_formatter ()



