
open Ast
open Types
open Util

(*  NOTES: 
   Cas particuier : dégager les @MTrue et remplacer par true
   Factoriser tous les (fprintf out_file)
   Varifier que la méthode actuelle fonctionne t-elle réellement sur des transitions sans arguments
   Les variables cubicle commencent par une majuscule, il faut le changer.
*)

(* Variables globales utilisées *)

let tmp_file_name = "sim_tmp.ml"

let get_value_for_type ty = 
  match (Hstring.view ty) with 
  | "int" -> "0"
  | "real" -> "0."
  | "bool" -> "true"
  | "proc" -> "get_random_proc ()"
  | _ -> "On doit ici prendre un array de toute les valeurs tu type énuméré et en prendre un random dedans... -> On doit donc stocker les déclarations de types"

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

let write_vars out_file s =
  let write_global (loc, name, t) =
    Printf.fprintf out_file "let %s = %s" (Hstring.view name) (get_value_for_type t);
    Printf.fprintf out_file "\n"
  in
  let write_const (loc, name, t) = 
    Printf.fprintf out_file "let %s = %s" (Hstring.view name) (get_value_for_type t);
    Printf.fprintf out_file "\n"
  in
  let write_array (loc, name, t) =
    Printf.fprintf out_file "let %s = Array.make (get_nb_proc ()) 0" (Hstring.view name); (* Ici le cas va être complexe ^^ *)
    Printf.fprintf out_file "\n"
  in
  
  List.iter write_global s.globals;
  List.iter write_const s.consts;
  List.iter write_array s.arrays

  
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
  write_vars out_file s;
  write_transitions out_file ts.t_trans;
  close_out out_file;
  exit 0
