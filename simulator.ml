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

let deplier_var_list var_list = 
  List.fold_left (fun prev v -> sprintf "%s.(%s)" prev (Hstring.view v)) "" var_list

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

(* TODO : On peut remplacer print_cs par un printf cs_to_string *)
let print_cs cs = 
  MConst.iter (fun k v -> match k with 
  | ConstInt(i) -> 
      let tmp = Num.int_of_num i in 
      fprintf out_file "%d" (tmp*v)
  | _ -> assert false)
  cs

let cs_to_string cs =
  MConst.fold (fun k v prev -> match k with 
  | ConstInt(i) -> 
      let tmp = Num.int_of_num i in 
    sprintf "%d%s" tmp prev
  | ConstReal(i) ->
      let tmp = Num.float_of_num i in 
      sprintf "%f%s" tmp prev
  |_ -> assert false
  ) 
  cs "" 

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

(* Les fonctions suivantes permettent de factoriser énormément de code. Elles permettent d'itérer sur des atoms et de les écrire facilement pour différent scénario possible *)
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
    | True -> fprintf out_file "%strue%s" mid_term end_term
    | False -> fprintf out_file "%sfalse%s" mid_term end_term
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
      | Comp(Elem(e1, _), Eq, Const(e2)) | Comp(Const(e2), Eq, Elem(e1,_)) -> union e1 (Hstring.make (cs_to_string e2))
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
          fprintf out_file "\t%s := %s;\n" (get_var_name head) (get_random_for_type t ty_defs); 
          with Not_found -> ()
        );
      let tail = Hstring.HSet.filter (fun v -> v <> head) set in 
      Hstring.HSet.iter (fun v -> fprintf out_file "\t%s := %s;\n" (get_var_name v) (!header)) tail;
    in
    List.iter write_union_find (!unionfindlist);
    (* END : UNION-FIND *)

    (* 
       TODO : Il faut filtrer le acess_set en fonction des variables, on peut penser a créer une Hashtbl avec les variables qui  composent l'accès. 
       On peut ensuite les regrouper en fonction de ces variables. 
       On peut également penser a faire une première passe qui, tant qu'a regrouper toutes les acces avec les mêmes variables, permet également de voir quelles sont les variables initialisée et 
       quelles sont les variables qui ne le sont pas. 
       On peut même faire une passe globale pour les variables également ?
       TODO : Attribution non déterministe des tableaux
    *)
    List.iter (fun var -> fprintf out_file "\tfor %s = 0 to get_nb_proc () do \n" (Hstring.view var)) vars;
    let write_access = function 
      | Comp(Access(g_var,var_list), _, other) | Comp(other,_, Access(g_var,var_list)) ->
          let access_value = 
            begin match other with
            | Elem(name, Glob) -> sprintf "!%s" (get_var_name name)
            | Elem(name, Constr) -> Hstring.view name 
            | Const(c) -> cs_to_string c
            | _ -> ""
            end in
          fprintf out_file "\t\t%s%s <- %s;\n" (get_var_name g_var) (deplier_var_list var_list) access_value
      | _ -> ()
    in
    SAtom.iter write_access access_set;
    List.iter (fun _ -> fprintf out_file "\tdone;\n") vars;
    in
  List.iter manage_satom dnf;
  
  fprintf out_file "\t()\n\n"

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
  List.iter write_type (List.tl t_def); (* On prend ici la tl de t_def car le premier élément est la définition d'un type @Mbool qu'on ne va pas utiliser*)
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
    fprintf out_file "let %s = Array.make (get_nb_proc ()) %s\n" (get_var_name name) (get_value_for_type var_type ty_defs)
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
        
        (* On écrit le premier atome, puis tous les autres sont écrit avec un && write TODO : Ne pas faire ça. On peut s'inspirer du () pour faire un && true mais bon c'est pas des plus propre ! *)
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

    fprintf out_file "\n";

    (* Write Ac *)
    fprintf out_file "\nlet ac_%s args = \n" trans_name;
    write_args ();

    (* Ac_Assigne *)
    let write_assign (var_to_updt, new_value) =
      fprintf out_file "\t%s := " (get_var_name var_to_updt);
      begin
      match new_value with
        | UTerm(t) -> write_term t 
        | _ -> ()
      end ;
      fprintf out_file ";\n";
    in
    List.iter write_assign trans_info.tr_assigns;

    (* Ac_Nondets *)
    let write_nondet var_name =
      fprintf out_file "\t%s := %s;\n" (get_var_name var_name) (get_random_for_type (Hstring.HMap.find var_name g_vars) ty_defs)
    in
    List.iter write_nondet trans_info.tr_nondets;

    (* Ac_Updates *)

    let watomfundep tfromatom = 
      match tfromatom with 
      | Comp(_, Eq, _) -> ("","=", "")
      | _ -> ("","","")
    in 
    let write_switch last (satom, term) =
      if not last then   
        (
        Printf.fprintf out_file "if ";
        SAtom.iter (write_atom_with_dep watomfundep) satom;
        fprintf out_file " then "
        );
        write_term term;
        fprintf out_file "\n";
        if not last then 
        fprintf out_file "\t\t\telse "
    in
    let write_upd up =
      List.iter (fun arg -> fprintf out_file "\tfor %s = 0 to (get_nb_proc ()) do \n " (Hstring.view arg)) up.up_arg;
      fprintf out_file "\t\tlet newval = \n\t\t\t";
      (* On va déplier les switch avec une série de if else ici. Le dernier else ne doit pas être un if else mais seulement un else pour que la fonction soit bien typé, *)
      let reved = List.rev up.up_swts in
      let last_swts = List.hd reved in
      let swts_list = List.rev (List.tl reved) in
      List.iter (write_switch false) swts_list;
      write_switch true last_swts;
      fprintf out_file "\t\tin %s%s <- newval\n" (get_var_name up.up_arr) (deplier_var_list up.up_arg);
      List.iter (fun arg -> fprintf out_file "\tdone; \n") up.up_arg; 
    in 
    List.iter write_upd trans_info.tr_upds;
    fprintf out_file "\t()\n";

    (* On écrit la transition pour la table *)
    fprintf out_file "\nlet %s = (\"%s\", req_%s, ac_%s) \n\n" trans_name trans_name trans_name trans_name
  in
  List.iter write_transition trans_list;
  
  (* écriture de la table de transition *) 

  fprintf out_file "\nlet build_table = \n";

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
