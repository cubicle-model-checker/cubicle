open Ast
open Types
open Util
open Atom

(* NOTES: 
  Vérifier s'il est possible de factoriser tous les (Printf.fprintf out_file)

  TODO : Implémentation des array 
  TODO : Implémentation d'init avec les constantes
  TODO : Implémentation de l'union find dans l'init
  TODO : Implémentation des booléens 
*)

(* Variables globales utilisées *)

let tmp_file_name = "simulator/stmp.ml"        (* Fichier sortie vers lequel le fichier cubicle va être compilé. Doit avoir un suffixe en ".ml" *)
let out_file = open_out tmp_file_name   
let var_prefix = "v"                    (* Préfixe pour les noms de variable. Nécéssaire car les variables cubicle commencent par une majuscule. *)


(* Fonctions d'aides *)
let get_var_name v = Format.sprintf "%s%s" var_prefix (Hstring.view v)
let print_hstring hs = Printf.fprintf out_file "%s" (Hstring.view hs)

(* Utilisé pour renvoyer une valeur d'initialisation quelconque avec le bon type pour une variable *)
let get_value_for_type ty ty_defs = 
  match (Hstring.view ty) with 
  | "int" | "proc" -> "0"
  | "real" -> "0."
  | "bool" -> "true"
  | _ ->
      let key = (Hstring.view ty) in
      let len = (Hashtbl.length ty_defs) in
      Printf.printf "%s %d" key len;
      Hstring.view (List.hd (Hashtbl.find ty_defs ty)) 

let write_term = function
  | Elem(g_var, Glob) -> Printf.fprintf out_file "%s" (get_var_name g_var)
  | Elem(g_var, Constr) -> Printf.fprintf out_file "%s" (Hstring.view g_var)
  | _ -> ()

let hstring_list_to_string hsl =
  let rec sub_hsllts hsl_rem prev =
    match hsl_rem with
      | [] -> ""
      | hd::tl -> Format.sprintf "%s%s%s" prev (Hstring.view hd) (sub_hsllts tl "; ")
  in 
  
  Format.sprintf "[%s]" (sub_hsllts hsl "")


let write_atom_with_fun first_term mid_term end_term f = function 
    | Comp(t1, Eq, t2) ->
        begin
        match t1, t2 with
        | Elem(g_var, Glob), Elem(constr, Constr) | Elem(constr, Constr), Elem(g_var, Glob) -> f g_var; Printf.fprintf out_file "%s%s%s%s%s" first_term (get_var_name g_var) mid_term (Hstring.view constr) end_term
        | Const(c), Elem(g_var, Glob) | Elem(g_var, Glob), Const(c) -> f g_var;  Printf.fprintf out_file "(* TODO : Initialisation d'une constante pour %s *)\n" (Hstring.view g_var)
        | _ -> ()
        end
    |_ -> ()

let write_atom first_term mid_term end_term = write_atom_with_fun first_term mid_term end_term (fun g_var -> ())

let get_random_for_type ty ty_defs =
  match (Hstring.view ty) with
  | "int" -> "Random.int 0" (* TODO : Fing max_int & min_int *)
  | "proc" -> "get_random_proc ()"
  | "real" -> "Random.float 0" (* TODO : Find max_float & min_float *)
  | "bool" -> "Random.bool ()"
  | _-> 
      let possible = Hashtbl.find ty_defs ty in 
      Format.sprintf "get_random_in_list %s" (hstring_list_to_string possible)

(* init
   simple analyse de dépendance avec union find
   sans array, sans arith

  gérer uniquement les égalité et les random

  gérer les formules avec les forall 

   variable aléatoire en finction du type

  Transition : ignorer les lets
  Gérer les UCase plus tard
  nondets utilisé uniquelent pour le sprocessus

  switch : casecade de if plutôt qu'on match

  fuzzing cubicle pour ne pas choisir les prochaines étapes par rapport au random

*)

(* Déclaration de l'init *)
let write_init (vars, dnf) g_vars ty_defs =
  Printf.fprintf out_file "let init () = \n";
  let written_var = ref Hstring.HSet.empty in
  let register_written_var g_var = written_var := Hstring.HSet.add g_var (!written_var) in
  let manage_satom = SAtom.iter (write_atom_with_fun "\t" " := " "\n" register_written_var) in
  (* Pour faire un init efficace, on doit regarde tous les sous atomes :
    Si on a une variable globale a gauche et un constructeur a droite, c'est une affectation
    TODO : Si on a une variable globale a gauche et une autre a droite, c'est une création d'une relation de dépendance
  *)
  (* TODO : Regarder els éléments dans g_vars keys qui ne sont pas dans written_var, et leurs associer une valeur au hasard pour leur type *)
  List.iter manage_satom dnf;
  let to_write = Hstring.HMap.filter (fun k v -> not (Hstring.HSet.mem k (!written_var))) g_vars in 
  let init_undet n t = 
    Printf.fprintf out_file ";\n\t %s := %s" (get_var_name n) (get_random_for_type t ty_defs)  
    in
  Hstring.HMap.iter init_undet to_write ;
  Printf.fprintf out_file "\n"

(* Déclaration des types *)

let write_types t_def =
  let returned = Hashtbl.create 124 in
  let print_type hs = Printf.fprintf out_file " | "; (print_hstring hs) in
  let write_possible_type hstring_list = List.iter print_type hstring_list in
  let write_type (loc, (t_name, t_values)) = 
    Printf.fprintf out_file "type %s = " (Hstring.view t_name);
    print_hstring (List.hd t_values);
    write_possible_type (List.tl t_values);
    Printf.fprintf out_file "\n";
    Hashtbl.add returned t_name t_values
  in
  List.iter write_type (List.tl t_def); (* On prend ici la tl de t_def car le premier élément est la définition d'un type @M bool qu'on ne va pas utiliser*)
  Printf.fprintf out_file "\n";
  returned

(* Déclaration des variables *)

(* Au lieu de retourner simplement une liste de toutes les variables, devrait renvoyer une map avec comme clef le nom de la variable et comme value le type de cette variable *)
let write_vars s ty_defs=
  let returned = ref Hstring.HMap.empty in
  let add_to_map n t = returned := (Hstring.HMap.add n t (!returned)) in
  let write_global (loc, name, var_type) =
    add_to_map name var_type;
    Printf.fprintf out_file "let %s = ref %s\n" (get_var_name name) (get_value_for_type var_type ty_defs)
  in
  let write_const (loc, name, var_type) = 
    add_to_map name var_type;
    Printf.fprintf out_file "let %s = ref %s\n" (get_var_name name) (get_value_for_type var_type ty_defs)
  in
  let write_array (loc, name, var_type) =
    (* TODO : Voir comment sont typé les arrays add_to_list name var_type; *)
    Printf.fprintf out_file "let %s = Array.make (get_nb_proc ()) 0\n" (get_var_name name) (*Pourquoi le var_type d'un array est en type*type ?*)
  in
  List.iter write_global s.globals;
  List.iter write_const s.consts;
  List.iter write_array s.arrays;
  Printf.fprintf out_file "\n";
  !returned

(* Déclaration des transitions *)
let write_transitions trans_list ty_defs g_vars =
  let write_transition trans =
    let trans_info = trans.tr_info in
    let trans_name = Hstring.view trans_info.tr_name in
    (* Write Req *)
    (* tr_reqs : Garde, tr_ureqs : Garde sur universally quantified *)
    Printf.fprintf out_file "let req_%s args = \n\t" trans_name;
    begin
      match SAtom.is_empty trans_info.tr_reqs with 
      | true -> Printf.fprintf out_file "true"
      | false -> 
        let first_atom = SAtom.choose trans_info.tr_reqs in
        let req_without_first = SAtom.remove first_atom trans_info.tr_reqs in
        
        (* On écrit le premier atome, puis tous les autres sont écrit avec un && write *)
        write_atom "\t(!" ") = " "" first_atom;
        SAtom.iter (write_atom " && (!" ") = " "") req_without_first
    end; 

    (* Write Ac *)
    Printf.fprintf out_file "\nlet ac_%s args = \n" trans_name;

    (* Ac_Assigne *)
    Printf.fprintf out_file "\tlet assign () =\n\t\t";
    let write_assign (var_to_updt, new_value) =
      Printf.fprintf out_file "%s := " (get_var_name var_to_updt);
      begin
      match new_value with
        | UTerm(t) -> write_term t 
        | _ -> ()
      end in
    let write_assign_and tr =
      Printf.fprintf out_file ";\n\t\t";
      write_assign tr
    in
    begin
      match (List.length trans_info.tr_assigns == 0) with (* TODO  : Ici on peut économiser légerement en faisant un is_empty plutôt que de regarder tout le count *)
      | true -> Printf.fprintf out_file "()"
      | false -> 
        let assign_hd = List.hd trans_info.tr_assigns in
        let assign_tl = List.tl trans_info.tr_assigns in
        
        (* On écrit le premier atome, puis tous les autres sont écrit avec un && write *)
        write_assign assign_hd;
        List.iter (write_assign_and) assign_tl
    end;
    Printf.fprintf out_file "\n\tin\n";

    (* Ac_Nondets *)
    Printf.fprintf out_file "\tlet nondets () =\n\t\t";
    let write_nondet var_name =
      Printf.fprintf out_file "%s := %s" (get_var_name var_name) (get_random_for_type (Hstring.HMap.find var_name g_vars) ty_defs)
    in
    let write_nondet_and var_name =
      Printf.fprintf out_file ";\n\t\t";
      write_nondet var_name
    in
    begin 
      match (List.length trans_info.tr_nondets == 0) with 
      | true -> Printf.fprintf out_file "()"
      | false -> 
        let nondet_hd = List.hd trans_info.tr_nondets in 
        let nondet_tl = List.tl trans_info.tr_nondets in
        write_nondet nondet_hd;
        List.iter write_nondet_and nondet_tl
    end;
    Printf.fprintf out_file "\n\tin\n";

    Printf.fprintf out_file " assign (); nondets ()";
    
    (* Write transition for table *)
    Printf.fprintf out_file "\nlet %s = (\"%s\", req_%s, ac_%s) \n\n" trans_name trans_name trans_name trans_name
  in
  List.iter write_transition trans_list;
  Printf.fprintf out_file "\n";
  Printf.fprintf out_file "let build_table = \n";

  let write_table trans = 
    let trans_info = trans.tr_info in
    let trans_name = Hstring.view trans_info.tr_name in
    Printf.fprintf out_file "\tadd_req_acc %s %s;\n" (string_of_int (List.length trans_info.tr_args)) trans_name
  in
  List.iter write_table trans_list;
  Printf.fprintf out_file "\n"

let run ts s =
  Printf.fprintf out_file "%s\n" "open Shelp";
  let g_types = write_types s.type_defs in
  let g_vars = write_vars s g_types in
  write_init ts.t_init g_vars g_types;
  write_transitions ts.t_trans g_types g_vars;
  close_out out_file;
  exit 0
