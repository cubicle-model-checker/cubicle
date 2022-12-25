open Ast
open Types
open Util
open Atom
open Printf

(* NOTES: 
  TODO : Implémentation des update d'array 
  TODO : Implémentation de l'union find dans l'init
  TODO : Tenter de compiler un programme cubicle avec uniquement des attribution non déterministe dans l'init et regarder le résultat 
  TODO : Essayer de factoriser les boucles for dans l'init
*)

(* Variables globales utilisées *)

let tmp_file_name = "simulator/stmp.ml"   (* Fichier sortie vers lequel le fichier cubicle va être compilé. Doit avoir un suffixe en ".ml" *)
let out_file = open_out tmp_file_name  
let var_prefix = "v"                      (* Préfixe pour les noms de variable. Nécéssaire car les variables cubicle commencent par une majuscule. *)

(* Fonctions d'aides *)
let get_var_name v = Format.sprintf "%s%s" var_prefix (Hstring.view v)
let print_hstring hs = fprintf out_file "%s" (Hstring.view hs)

(* Utilisé pour renvoyer une valeur d'initialisation quelconque avec le bon type pour une variable *)
let get_value_for_type ty ty_defs = 
  match (Hstring.view ty) with 
  | "int" | "proc" -> "0"
  | "real" -> "0."
  | "bool" | "mbool" -> "true"
  | _ -> Hstring.view (List.hd (Hashtbl.find ty_defs ty)) (* Note : Hashtbl.find ne devrait pas throw Not_Found car ast valide. *) 


let hstring_list_to_string hsl =
  let rec sub_hsllts hsl_rem prev =
    match hsl_rem with
      | [] -> ""
      | hd::tl -> Format.sprintf "%s%s%s" prev (Hstring.view hd) (sub_hsllts tl "; ")
  in 
  
  Format.sprintf "[%s]" (sub_hsllts hsl "")

let print_const = function
  | ConstInt n | ConstReal n -> fprintf out_file "%s" (Num.string_of_num n)
  | ConstName n -> fprintf out_file "%s" (Hstring.view n) 

let print_cs cs = 
  MConst.iter (fun k v -> match k with 
  | ConstInt(i) -> 
      let tmp = Num.int_of_num i in 
      fprintf out_file "%d" (tmp*v)
  | _ -> assert false)
  cs 

let write_term = function
  | Elem(g_var, Glob) -> fprintf out_file "%s" (get_var_name g_var)
  | Elem(var, _) -> 
      let s = Hstring.view var in 
      let str = begin match s with 
      | "@MTrue" -> "true"
      | "@MFalse" -> "false"
      | _ -> s 
      end in 
      fprintf out_file "%s" str
  | Const(c) -> print_cs c
  | Access(g_var, var_list) -> 
      fprintf out_file "%s" (get_var_name g_var); (* TODO : Array a plus d'une dimension *)
      List.iter (fun var -> fprintf out_file ".(%s)" (Hstring.view var)) var_list
  | _ -> () 

let write_atom_with_fun first_term mid_term end_term f = function 
    | Comp(t1, Eq, t2) ->
        begin
          let t1, t2 = begin
            match t1, t2 with
            | (Elem(g_var, Glob) as t1), (Elem(constr, Constr) as t2) | (Elem(constr, Constr) as t2), (Elem(g_var, Glob) as t1) -> f g_var; t1, t2
            | (Const(c) as t2), (Elem(g_var, Glob) as t1) | (Elem(g_var, Glob) as t1), (Const(c) as t2) -> f g_var; t1, t2
            | (Access(g_var, var_list) as t1), (Const(c) as t2) | (Const(c) as t2), (Access(g_var, var_list) as t1) -> f g_var; t1, t2
            | (Access(g_var, var_list) as t1), (Elem(constr, Constr) as t2) | (Elem(constr, Constr) as t2), (Access(g_var, var_list) as t1) -> f g_var; t1, t2
            |   _ -> t1, t2
          end in
        fprintf out_file "%s" first_term;
        write_term t1;
        fprintf out_file "%s" mid_term;
        write_term t2;
        fprintf out_file "%s" end_term
        end
    | True -> printf "true ?\n"
    | False -> printf "fales ? \n"
    | _ -> ()

let write_atom_with_fun_dep t_from_atom f atom =
  let ft,mt,et = t_from_atom atom in 
  write_atom_with_fun ft mt et f atom

let write_atom first_term mid_term end_term = write_atom_with_fun first_term mid_term end_term (fun g_var -> ())

let write_atom_with_dep t_from_atom = write_atom_with_fun_dep t_from_atom (fun g_var -> ())

let get_random_for_type ty ty_defs =
  match (Hstring.view ty) with
  | "int" -> "Random.int max_int" 
  | "proc" -> "get_random_proc ()"
  | "real" -> "Random.float max_float"
  | "bool" | "mbool" -> "Random.bool ()"
  | _-> 
      let possible = Hashtbl.find ty_defs ty in 
      Format.sprintf "get_random_in_list %s" (hstring_list_to_string possible)

(* Déclaration de l'init *)
let write_init (vars, dnf) g_vars ty_defs =
  fprintf out_file "let init () = \n";
  let written_var = ref Hstring.HSet.empty in
  let register_written_var g_var = written_var := Hstring.HSet.add g_var (!written_var) in
  let manage_satom satom =
      if not (SAtom.is_empty satom) then 
        begin
          let hd = SAtom.choose satom in 
          let tl = SAtom.remove hd satom in
          let choose_t_from_atom_first = function
            | Comp(Access(_,var_list), _, _) | Comp(_,_, Access(_,var_list)) -> 
                let vl = Hstring.view (List.hd var_list) in 
                Format.sprintf "\tfor %s = 0 to get_nb_proc () do \n\t\t" vl, " <- ", "\n\tdone"
            | _ -> "\t"," := ", ""
          in
          write_atom_with_fun_dep choose_t_from_atom_first register_written_var hd;
          let choose_t_from_atom_other = function
            | Comp(Access(_,var_list), _, _) | Comp(_,_, Access(_,var_list)) -> 
                let vl = Hstring.view (List.hd var_list) in 
                Format.sprintf ";\n\tfor %s = 0 to get_nb_proc () do \n\t\t" vl, " <- ", "\n\tdone"
            | _ -> ";\n\t"," := ", ""
          in
          SAtom.iter (write_atom_with_fun_dep choose_t_from_atom_other register_written_var) tl
        end
      else
        fprintf out_file "()"
    in
  
  List.iter manage_satom dnf;

  (* Toutes les valeurs qui n'ont pas une valeur explicite doivent tout de même être initialisée *)
  let to_write = Hstring.HMap.filter (fun k v -> not (Hstring.HSet.mem k (!written_var))) g_vars in 
  let init_undet n t = 
    fprintf out_file ";\n\t%s := %s" (get_var_name n) (get_random_for_type t ty_defs)  
    in
  Hstring.HMap.iter init_undet to_write ;
  fprintf out_file "\n"

(* Déclaration des types *)

let write_types t_def =
  let returned = Hashtbl.create 124 in (* NOTE : 124 choisi ici arbitrairement de façon aléatoire. *)
  let print_type hs = Printf.fprintf out_file " | "; (print_hstring hs) in
  let write_possible_type hstring_list = List.iter print_type hstring_list in
  let write_type (loc, (t_name, t_values)) = 
    fprintf out_file "type %s = " (Hstring.view t_name);
    print_hstring (List.hd t_values);
    write_possible_type (List.tl t_values);
    fprintf out_file "\n";
    Hashtbl.add returned t_name t_values
  in
  List.iter write_type (List.tl t_def); (* On prend ici la tl de t_def car le premier élément est la définition d'un type @M bool qu'on ne va pas utiliser*)
  fprintf out_file "\n";
  returned

(* Déclaration des variables *)

(* Renvoie une map avec comme clef le nom des variables et comme values leurs types *)
let write_vars s ty_defs=
  let returned = ref Hstring.HMap.empty in
  let add_to_map n t = returned := (Hstring.HMap.add n t (!returned)) in
  let write_global (loc, name, var_type) =
    add_to_map name var_type;
    fprintf out_file "let %s = ref %s\n" (get_var_name name) (get_value_for_type var_type ty_defs)
  in
  let write_const (loc, name, var_type) = 
    add_to_map name var_type;
    fprintf out_file "let %s = ref %s\n" (get_var_name name) (get_value_for_type var_type ty_defs)
  in
  let write_array (loc, name, (dim, var_type)) =
    (* let array_dim = List.length l in *)
    fprintf out_file "let %s = Array.make (get_nb_proc ()) %s\n" (get_var_name name) (get_value_for_type var_type ty_defs) (*Pourquoi le var_type d'un array est en type*type ?*)
  in
  List.iter write_global s.globals;
  List.iter write_const s.consts;
  List.iter write_array s.arrays;
  fprintf out_file "\n";
  !returned

(* Déclaration des transitions *)
let write_transitions trans_list ty_defs g_vars =
  let write_transition trans =
    let trans_info = trans.tr_info in
    let trans_name = Hstring.view trans_info.tr_name in

    (* Write arguments *)
    
    let trans_args = trans_info.tr_args in 
    let write_args () = (* On va re écrire les arguments dans le req et dans le ac, donc on le fait en une fonction *)
    begin 
      let count = ref 0 in
      let write_args arg = 
        begin 
          fprintf out_file "\tlet %s = find_ieme args %d in\n" (Hstring.view arg) (!count);
          count := (!count) + 1; 
        end in
      List.iter write_args trans_args;
    end in

    (* Write Req *)
    (* tr_reqs : Garde, tr_ureqs : Garde sur universally quantified *)
    fprintf out_file "let req_%s args = \n" trans_name;
    begin
      match SAtom.is_empty trans_info.tr_reqs with 
      | true -> Printf.fprintf out_file "\ttrue"
      | false -> 
        write_args ();
        let first_atom = SAtom.choose trans_info.tr_reqs in
        let req_without_first = SAtom.remove first_atom trans_info.tr_reqs in
        
        (* On écrit le premier atome, puis tous les autres sont écrit avec un && write *)
        let choose_t_from_atom_first = function
        | Comp(Access(_,_), _, _) | Comp(_, _, Access(_,_)) -> "\t"," = ",""
        | _ -> "\t(!",") = ",""
        in
        write_atom_with_dep choose_t_from_atom_first first_atom;
        let choose_t_from_atom_other = function
        | Comp(Access(_,_), _, _) | Comp(_, _, Access(_,_)) -> " && "," = ",""
        | _ -> " && (!",") = ",""
        in
        SAtom.iter (write_atom_with_dep choose_t_from_atom_other) req_without_first;

    end; 

    (* Write Ac *)
    fprintf out_file "\nlet ac_%s args = \n" trans_name;
    write_args ();

    (* Ac_Assigne *)
    fprintf out_file "\tlet assign () =\n\t\t";
    let write_assign (var_to_updt, new_value) =
      fprintf out_file "%s := " (get_var_name var_to_updt);
      begin
      match new_value with
        | UTerm(t) -> write_term t 
        | _ -> ()
      end in
    let write_assign_and tr =
      fprintf out_file ";\n\t\t";
      write_assign tr
    in
    begin match (List.length trans_info.tr_assigns == 0) with (* TODO  : Ici on peut économiser légerement en faisant un is_empty plutôt que de regarder tout le count *)
      | true -> fprintf out_file "()"
      | false -> 
        let assign_hd = List.hd trans_info.tr_assigns in
        let assign_tl = List.tl trans_info.tr_assigns in
        
        (* On écrit le premier atome, puis tous les autres sont écrit avec un && write *)
        write_assign assign_hd;
        List.iter (write_assign_and) assign_tl
    end;
    fprintf out_file "\n\tin\n";

    (* Ac_Nondets *)
    fprintf out_file "\tlet nondets () =\n\t\t";
    let write_nondet var_name =
      fprintf out_file "%s := %s" (get_var_name var_name) (get_random_for_type (Hstring.HMap.find var_name g_vars) ty_defs)
    in
    let write_nondet_and var_name =
      fprintf out_file ";\n\t\t";
      write_nondet var_name
    in
    begin match (List.length trans_info.tr_nondets == 0) with 
    | true -> fprintf out_file "()"
    | false -> 
      let nondet_hd = List.hd trans_info.tr_nondets in 
      let nondet_tl = List.tl trans_info.tr_nondets in
      write_nondet nondet_hd;
      List.iter write_nondet_and nondet_tl
    end;
    fprintf out_file "\n\tin\n";

    (* Ac_Updates *)
    fprintf out_file "\tlet update () = \n\t\t";

    let write_upd up =
      fprintf out_file "let val = "; (* Déplier les switch ici pour associer une valeur a val*)
      printf "%d" (List.length up.up_arg);
      fprintf out_file "in %s.(%s) <- val\n" (get_var_name up.up_arr) (Hstring.view (List.hd up.up_arg));
      List.iter (fun (satom, term) -> write_term term; fprintf out_file " "; SAtom.iter (write_atom "" "" "\n" ) satom) up.up_swts;
      

    in 
    let write_upd_and up = write_upd up in 

    begin match (List.length trans_info.tr_upds == 0) with 
    | true -> fprintf out_file "()"
    | _ -> 
        let upd_hd = List.hd trans_info.tr_upds in 
        let upd_tl = List.tl trans_info.tr_upds in 
        write_upd upd_hd;
        List.iter write_upd_and upd_tl
    end;
    fprintf out_file "\n\tin\n";

    (* End *)
    fprintf out_file " assign (); nondets (); update ()";
    
    (* Write transition for table *)
    fprintf out_file "\nlet %s = (\"%s\", req_%s, ac_%s) \n\n" trans_name trans_name trans_name trans_name
  in
  List.iter write_transition trans_list;
  fprintf out_file "\n";
  fprintf out_file "let build_table = \n";

  let write_table trans = 
    let trans_info = trans.tr_info in
    let trans_name = Hstring.view trans_info.tr_name in
    fprintf out_file "\tadd_req_acc %s %s;\n" (string_of_int (List.length trans_info.tr_args)) trans_name
  in
  List.iter write_table trans_list;
  fprintf out_file "\n"

let run ts s =
  fprintf out_file "%s\n" "open Shelp";
  let g_types = write_types s.type_defs in
  let g_vars = write_vars s g_types in
  write_init ts.t_init g_vars g_types;
  write_transitions ts.t_trans g_types g_vars;
  close_out out_file;
  exit 0
