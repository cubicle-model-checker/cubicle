open Ast
open Types
open Util
open Atom
open Printf

(* Quelques notes qui valent pour toutes les fonctions du fichier: 
  En général, les fonctions sont des séquences d'instruction.
  On écrit une instruction en considérant que il y a une autre instruction qui va suivre. 
  On l'écrit également en considérant qu'on est sur une nouvelle ligne. On va donc généralement finir les ligne par ';\n'.
  On va en genéral finir toutes les fonctions de type unit par "()". Si il n'y a aucune instruction avant, ça marchera quand même, et si il y en a ça permet d'avoir une instruction finale.
  C'est une solution beaucoup plus simple que de séparer les premières instruction de la dernière, créant un code pour le compilateur plus complexe.
*)

(* Variables globales utilisées *)

let tmp_file_name = "simulator/stmp.ml"   (* Fichier sortie vers lequel le fichier cubicle va être compilé. Doit avoir un suffixe en ".ml" *)
let out_file = open_out tmp_file_name  
let var_prefix = "v"                      (* Préfixe pour les noms de variable. Nécéssaire car les variables cubicle commencent par une majuscule, impossible en caml *)
let pfile = fun d -> fprintf out_file d

(* BEGIN : Fonction d'aide ; Peut être a déplacer dans un fichier 'clib.ml' *)
let get_var_name v = Format.sprintf "%s%s" var_prefix (Hstring.view v)
let get_constr_name s = 
  let s = Hstring.view s in match s with
    | "@MTrue" -> "true"
    | "@MFalse" -> "false"
    | _ -> s 
let print_hstring hs = pfile "%s" (Hstring.view hs)

(* Utilisé pour renvoyer une valeur d'initialisation quelconque avec le bon type pour une variable *)
let get_value_for_type ty ty_defs = 
  match (Hstring.view ty) with 
  | "int" | "proc" -> "0"
  | "real" -> "0."
  | "bool" | "mbool" -> "true"
  | _ -> Hstring.view (List.hd (Hashtbl.find ty_defs ty)) (* Note : Hashtbl.find ne devrait pas throw Not_Found car ast valide. *) 

let deplier_var_list var_list = 
  List.fold_left (fun prev v -> sprintf "%s.(%s)" prev (Hstring.view v)) "" var_list

let hstring_list_to_string hsl =
  let rec sub_hsllts hsl_rem prev =
    match hsl_rem with
      | [] -> ""
      | hd::tl -> Format.sprintf "%s%s%s" prev (Hstring.view hd) (sub_hsllts tl "; ")
  in 
  Format.sprintf "[%s]" (sub_hsllts hsl "")

let const_to_string = function 
  | ConstInt n -> sprintf "%s" (Num.string_of_num n)
  | ConstReal n -> sprintf "%s." (Num.string_of_num n)
  | ConstName n -> sprintf "%s" (get_var_name n)

let print_const cs = pfile "%s" (const_to_string cs)

(* FIXME Le cs to string actuellement ne marche pas vraiment : Il n'y a pas les symboles '*' et '+' *)
let mconst_to_string cs =
  MConst.fold (fun k v prev -> sprintf "%s%s" (const_to_string k) prev) cs ""

let print_mconst = fun cs -> pfile "%s" (mconst_to_string cs)

let print_term = function
  | Elem(g_var, Glob) -> pfile "%s" (get_var_name g_var)
  | Elem(var, _) -> pfile "%s" (get_constr_name var)
  | Const(c) -> print_mconst c
  | Access(g_var, var_list) -> 
      pfile "%s" (get_var_name g_var); 
      List.iter (fun var -> pfile ".(%s)" (Hstring.view var)) var_list
  | _ -> () 

let get_random_for_type ty ty_defs =
  match (Hstring.view ty) with
  | "int" -> "Random.int max_int" 
  | "proc" -> "get_random_proc ()"
  | "real" -> "Random.float max_float"
  | "bool" | "mbool" -> "Random.bool ()"
  | _-> 
      let possible = Hashtbl.find ty_defs ty in 
      Format.sprintf "get_random_in_list %s" (hstring_list_to_string possible)

(* END : Fonction d'aide *)

(* Déclaration des types *)

let write_types t_def =
  let returned = Hashtbl.create (List.length t_def) in 
  let print_type hs = pfile " | "; (print_hstring hs) in
  let write_possible_type hstring_list = List.iter print_type hstring_list in
  let write_type (loc, (t_name, t_values)) = 
    pfile "type %s = " (Hstring.view t_name);
    print_hstring (List.hd t_values);
    write_possible_type (List.tl t_values);
    pfile "\n";
    Hashtbl.add returned t_name t_values
  in
  List.iter write_type (List.tl t_def); (* On prend ici la tl de t_def car le premier élément est la définition d'un type @Mbool qu'on ne va pas utiliser*)
  pfile "\n";
  returned

(* Déclaration des variables *)

(* Renvoie une map avec comme clef le nom des variables et comme values leurs types *)
let write_vars s ty_defs =
  let returned = ref Hstring.HMap.empty in
  let add_to_map n t = returned := (Hstring.HMap.add n t (!returned)) in
  let write_global (loc, name, var_type) =
    add_to_map name var_type;
    pfile "let %s = ref %s\n" (get_var_name name) (get_value_for_type var_type ty_defs)
  in
  let write_const (loc, name, var_type) = 
    add_to_map name var_type;
    pfile "let %s = ref %s\n" (get_var_name name) (get_value_for_type var_type ty_defs) (* Note : les const n'ont pas réellement besoin d'être des ref *)
  in
  let write_array (loc, name, (dim, var_type)) =
    pfile "let %s = " (get_var_name name);
    List.iter (fun _ -> pfile "Array.make (get_nb_proc ()) (") dim;
    pfile "%s" (get_value_for_type var_type ty_defs);
    List.iter (fun _ -> pfile ")") dim;
    pfile "\n"
  in
  List.iter write_global s.globals;
  List.iter write_const s.consts;
  List.iter write_array s.arrays;
  pfile "\n";
  !returned

(* Déclaration de l'init *)

let write_init (vars, dnf) g_vars ty_defs =
  pfile "let init () = \n";
  let written_var = ref Hstring.HSet.empty in
  let register_written_var g_var = written_var := Hstring.HSet.add g_var (!written_var) in
  let manage_satom satom =
    let is_access = function
      | Comp(Access(_,var_list), _, _) | Comp(_,_, Access(_,var_list)) -> true
      | _ -> false 
    in 
    let (access_set, other_set) = SAtom.partition is_access satom in 
    
    (* BEGIN : UNION-FIND *)
    (* Note : Implémentation de l'Union-Find sous optimale. *)
  
    let unionfindlist = ref [] in
    Hstring.HMap.iter (fun k v -> unionfindlist := (Hstring.HSet.singleton k)::(!unionfindlist)) g_vars; 
    let find e = try List.find (fun s -> Hstring.HSet.exists (fun a -> a = e) s) (!unionfindlist) with Not_found -> Hstring.HSet.singleton e in
    let union e1 e2 = 
      let s1 = find e1 in 
      let s2 = find e2 in 
      let ns = Hstring.HSet.union s1 s2 in 
      let filtered = List.filter (fun s -> s <> s1 && s <> s2) (!unionfindlist) in 
      unionfindlist := ns::filtered
    in 
    let unionfind = function 
      | Comp(Elem(e1, _) , Eq, Elem(e2, _))  -> union e1 e2
      | Comp(Elem(e1, _), Eq, Const(e2)) | Comp(Const(e2), Eq, Elem(e1,_)) -> union e1 (Hstring.make (mconst_to_string e2))
      | _ -> assert false 
    in
    
    let find_head_in set =  (* Renvoie en priorité un constructeur, puis une variable sinon *)
      let is_constr v = not (Hstring.HMap.mem v g_vars) in
      try (Hstring.HSet.find_first is_constr set, true) with Not_found -> (Hstring.HSet.choose set, false)
    in 
    SAtom.iter unionfind other_set;
    let write_union_find set = 
      let (head, is_constr) = find_head_in set in
      (* Si head est un constr, toutes les valeurs suivantes prennent la valeur de head. Sinon on initialise une tête random *)
      let header = ref (Hstring.view head) in
      if not is_constr then
        (
          (* Si ce n'est pas une constante, on l'initialise. Sinon pas besoin *)
          try let t = Hstring.HMap.find head g_vars in
          header := sprintf "!%s" (get_var_name head);
          pfile "\t%s := %s;\n" (get_var_name head) (get_random_for_type t ty_defs); 
          with Not_found -> ()
        );
      let tail = Hstring.HSet.filter (fun v -> v <> head) set in 
      Hstring.HSet.iter (fun v -> register_written_var v; pfile "\t%s := %s;\n" (get_var_name v) (!header)) tail;
    in
    List.iter write_union_find (!unionfindlist);
    (* END : UNION-FIND *)

    (*
    TODO : On veut regrouper les acess en fonction de leurs var_list, et imbriquer les for correctement. 
    On fait par exemple :
      for i = 0 to get_nb_proc ():
        azek.(i) <- true 
        for j = 0 to get_nb_proc() :
          ribo.(i).(j) <- azek.(i)
    On peut penser a le faire avec une Hashtbl ou HSet 
    On peut dans cette même passe s'occuper de register_written_var.
    *)
    List.iter (fun var -> pfile "\tfor %s = 0 to get_nb_proc () do \n" (Hstring.view var)) vars;
    let write_access = function 
      | Comp(Access(g_var,var_list), _, other) | Comp(other,_, Access(g_var,var_list)) ->
          let access_value = 
            begin match other with
            | Elem(name, Glob) -> sprintf "!%s" (get_var_name name)
            | Elem(name, Constr) -> get_constr_name name 
            | Const(c) -> mconst_to_string c
            | _ -> ""
            end in
          register_written_var g_var;
          pfile "\t\t%s%s <- %s;\n" (get_var_name g_var) (deplier_var_list var_list) access_value
      | _ -> ()
    in
    SAtom.iter write_access access_set;
    (* TODO ICI : Attribution non déterministe pour les array restant *)
    List.iter (fun _ -> pfile "\tdone;\n") vars;
    in
  List.iter manage_satom dnf;
  
  pfile "\t()\n\n"

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
          pfile "\tlet %s = find_ieme args %d in\n" (Hstring.view arg) (!count);
          count := (!count) + 1; 
        end in
      List.iter write_args trans_args;
    end in

    (* Write Req *)
    (* tr_reqs : Garde, tr_ureqs : Garde sur universally quantified *)
    pfile "let req_%s args = \n" trans_name;
    write_args ();
        
    let print_op = function 
    | Eq -> pfile " = "
    | Le -> pfile " <= "
    | Lt -> pfile " < "
    | Neq -> pfile " <> "
    in
    let print_atom = function
    | Comp(t1, op, t2) -> 
      print_term t1;
      print_op op;
      print_term t2;
      pfile " && "
    | True -> pfile "true && "
    | False -> pfile "false && "
    | _ -> ()
    in
    SAtom.iter print_atom trans_info.tr_reqs;
    pfile "true\n\n";

    (* Write Ac *)
    pfile "let ac_%s args = \n" trans_name;
    write_args ();

    (* Ac_Assigne *)
    let write_assign (var_to_updt, new_value) =
      pfile "\t%s := " (get_var_name var_to_updt);
      begin
      match new_value with
        | UTerm(t) -> print_term t 
        | _ -> () (* TODO : Assignations par swts *)
      end ;
      pfile ";\n";
    in
    List.iter write_assign trans_info.tr_assigns;

    (* Ac_Nondets *)
    let write_nondet var_name =
      pfile "\t%s := %s;\n" (get_var_name var_name) (get_random_for_type (Hstring.HMap.find var_name g_vars) ty_defs)
    in
    List.iter write_nondet trans_info.tr_nondets;

    (* Ac_Updates *)

    let print_atom = function  
      | Comp(t1, Eq, t2) -> 
          begin
          print_term t1;
          pfile "=";
          print_term t2
          end
      | _ -> ()
    in 
    let write_switch last (satom, term) =
      if not last then   
        (
        pfile "if ";
        SAtom.iter (print_atom) satom;
        pfile " then "
        );
        print_term term;
        pfile "\n";
        if not last then 
        pfile "\t\t\telse "
    in
    let write_upd up =
      List.iter (fun arg -> pfile "\tfor %s = 0 to (get_nb_proc ()) do \n " (Hstring.view arg)) up.up_arg;
      pfile "\t\tlet newval = \n\t\t\t";
      (* On va déplier les switch avec une série de if else ici. Le dernier else ne doit pas être un if else mais seulement un else pour que la fonction soit bien typé, *)
      let reved = List.rev up.up_swts in
      let last_swts = List.hd reved in
      let swts_list = List.rev (List.tl reved) in
      List.iter (write_switch false) swts_list;
      write_switch true last_swts;
      pfile "\t\tin %s%s <- newval\n" (get_var_name up.up_arr) (deplier_var_list up.up_arg);
      List.iter (fun arg -> pfile "\tdone; \n") up.up_arg; 
    in 
    List.iter write_upd trans_info.tr_upds;
    pfile "\t()\n";

    (* On écrit la transition pour la table *)
    pfile "\nlet %s = (\"%s\", req_%s, ac_%s) \n\n" trans_name trans_name trans_name trans_name
  in
  List.iter write_transition trans_list;
  
  (* écriture de la table de transition *) 

  pfile "\nlet build_table = \n";

  let write_table trans = 
    let trans_info = trans.tr_info in
    let trans_name = Hstring.view trans_info.tr_name in
    pfile  "\tadd_req_acc %s %s;\n" (string_of_int (List.length trans_info.tr_args)) trans_name
  in
  List.iter write_table trans_list;
  pfile "\n"

let run ts s =
  pfile "%s\n" "open Shelp";
  let g_types = write_types s.type_defs in
  let g_vars = write_vars s g_types in
  write_init ts.t_init g_vars g_types;
  write_transitions ts.t_trans g_types g_vars;
  close_out out_file;
  exit 0
