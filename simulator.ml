
open Ast
open Types
open Util

(*  NOTES: 
   Cas particuier : dégager les @MTrue et remplacer par true
   Il y a sûrement un moyen de factoriser tous les fprintf out_file .... et le remplacer par une seule variable que l'on va set une bonne fois pour toute
   La méthode actuelle fonctionne t-elle réellement sur des transitions sans arguments ??
   Les variables qui ont un nom qui commence par une majuscule ne fonctionnent pas
*)

let tmp_file_name = "sim_tmp.ml"

(* Fonctions d'aide *)

let print_hstring out_file hs = Printf.fprintf out_file "%s" (Hstring.view hs)

(* Déclaration des types *)

let write_types out_file t_def =
  let print_type hs = Printf.fprintf out_file " | "; (print_hstring out_file hs) in
  let write_possible_type hstring_list = List.iter print_type hstring_list in
  let write_type (loc, (t_name, t_values)) = 
    Printf.fprintf out_file "type %s = " (Hstring.view t_name);
    print_hstring out_file (List.hd t_values);
    write_possible_type (List.tl t_values);
    Printf.fprintf out_file "\n"
  in
  List.iter write_type (List.tl t_def); (* On prend ici la tl de t_def car le premier élément est la définition d'un type @M bool qu'on ne va pas utiliser*)
  Printf.fprintf out_file "\n"
  
(* Déclaration des variables *)
let write_vars out_file ts =
  let write_global global =
    Printf.fprintf out_file "let %s = " (Hstring.view global);
    Printf.fprintf out_file "\n"
  in
  let write_const const = 
    Printf.fprintf out_file "let %s = " (Hstring.view const);
    Printf.fprintf out_file "\n"
  in
  let write_array array =
    Printf.fprintf out_file "let %s = Array.make (get_nb_proc ()) 0" (Hstring.view array);
    Printf.fprintf out_file "\n"
  in
  (*
  let print_tester (to_print_list, dnf) =
    Printf.fprintf out_file "%s" (string_of_int (List.length to_print_list)); 
    List.iter (print_hstring out_file) to_print_list
  in
  *)
  List.iter write_global ts.t_globals;
  List.iter write_const ts.t_consts;
  List.iter write_array ts.t_arrays

  
(* Déclaration des transitions *)
let write_transitions out_file trans_list =
  let write_transition trans =
    let trans_info = trans.tr_info in
    let trans_name = Hstring.view trans_info.tr_name in
    Printf.fprintf out_file "let req_%s args = \n" trans_name;
    Printf.fprintf out_file "let ac_%s args = \n" trans_name;
    Printf.fprintf out_file "let %s = (req_%s, ac_%s) \n" trans_name trans_name trans_name
  in
  List.iter write_transition trans_list;
  Printf.fprintf out_file "\n";
  Printf.fprintf out_file "let build_table = \n";
  let write_table trans = 
    let trans_info = trans.tr_info in
    let trans_name = Hstring.view trans_info.tr_name in
    Printf.fprintf out_file "\tadd_req_acc %s %s;\n" (string_of_int (List.length trans_info.tr_args)) trans_name
  in
  List.iter write_table trans_list

let run ts s =
  let out_file = open_out tmp_file_name in
  Printf.fprintf out_file "%s\n" "open Sim_usual";
  write_types out_file s.type_defs;
  write_vars out_file ts;
  write_transitions out_file ts.t_trans;
  close_out out_file;
  exit 0
