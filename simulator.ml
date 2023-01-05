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

  Les fonctions print_"..." écrivent dans le fichier destination. 
*)

(* Variables globales utilisées *)

let tmp_file_name = "simulator/stmp.ml"   (* Fichier sortie vers lequel le fichier cubicle va être compilé. Doit avoir un suffixe en ".ml" *)
let out_file = open_out tmp_file_name  
let var_prefix = "v"                      (* Préfixe pour les noms de variable. Nécéssaire car les variables cubicle commencent par une majuscule, impossible en caml *)
let updated_prefix = "n"                  (* Voir dans transition *)
let pfile = fun d -> fprintf out_file d

(* BEGIN : Fonction d'aide ; Peut être a déplacer dans un fichier 'clib.ml' *)
let get_var_name v = Format.sprintf "%s%s" var_prefix (Hstring.view v)
let get_updated_name v = Format.sprintf "%s%s" updated_prefix (Hstring.view v)
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

let mconst_is_float mconst g_vars  = 
  MConst.exists 
  (
    fun k v -> match k with 
    | ConstReal(_) -> true 
    | ConstName(n) -> 
        (try (let (t, d) = (Hstring.HMap.find n g_vars) in (Hstring.view t) = "real") with Not_found -> false)
    | _ -> false
  ) 
  mconst

let deplier_var_list var_list = 
  List.fold_left (fun prev v -> sprintf "%s.(%s)" prev (Hstring.view v)) "" var_list

(* Permet de multiplier le string s par le string n. Utile pour permettre la tabulation correcte. *)
let mult_string s n = 
  let reste = ref "" in 
  for i = 1 to n do 
    reste := s^(!reste)
  done;
  !reste

(* Permet d'accéder a un tableau de dimension n. Renvoie le string ".(tmp_0).(tmp_1)..." *)
let deplier_var n = 
  let reste = ref "" in 
  for i = 1 to n do 
    reste := (!reste)^(sprintf ".(tmp_%d)" (i-1))
  done;
  !reste

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

let mconst_to_string cs =
  MConst.fold 
  (
    fun k v prev -> 
      let nv = 
      match v with 
      | 1 -> sprintf "%s" (const_to_string k)
      | _ -> sprintf "(%s * %d)" (const_to_string k) v (* Note : Ici les parentèse dans le string ne sont pas réllement obligatoire mais je trouve que ça rend le code final plus lisible *) 
    in
    match prev with 
    | "" -> sprintf "%s" nv
    | _ -> sprintf "%s + %s" nv prev
  )
  cs ""

let const_ref_to_string = function
  | ConstInt n -> sprintf "%s" (Num.string_of_num n)
  | ConstReal n -> sprintf "%s." (Num.string_of_num n)
  | ConstName n -> sprintf "!(%s)" (get_var_name n)

let mconst_ref_to_string cs = 
  MConst.fold (fun k v prev -> sprintf "%s%s" (const_ref_to_string k) prev) cs ""

let print_mconst = fun cs -> pfile "%s" (mconst_to_string cs)
let print_mconst_ref = fun cs -> pfile "%s" (mconst_ref_to_string cs)

let rec print_term g_vars = function
  | Elem(g_var, Glob) -> pfile "!(%s)" (get_var_name g_var)
  | Elem(var, _) -> pfile "%s" (get_constr_name var)
  | Const(c) -> print_mconst_ref c
  | Access(g_var, var_list) -> 
      pfile "%s" (get_var_name g_var); 
      List.iter (fun var -> pfile ".(%s)" (Hstring.view var)) var_list
  | Arith(t, c) -> 
      print_term g_vars t; 
      let op = if (mconst_is_float c g_vars) then "+." else "+"  in
      pfile " %s " op; 
      print_mconst_ref c

let get_random_for_type ty ty_defs =
  match (Hstring.view ty) with
  | "int" -> "Random.int max_int" 
  | "proc" -> "get_random_proc ()"
  | "real" -> "Random.float max_float"
  | "bool" | "mbool" -> "Random.bool ()"
  | _-> 
      let possible = Hashtbl.find ty_defs ty in 
      Format.sprintf "get_random_in_list %s" (hstring_list_to_string possible)

let get_var_type var_name g_vars = let (t,_) = Hstring.HMap.find var_name g_vars in t
let get_var_dim var_name g_vars = try let (_, d) = Hstring.HMap.find var_name g_vars in d with Not_found -> -1

module IntMap = Map.Make(struct type t = int let compare : int -> int -> int = Int.compare end) 

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
  let add_to_map n t dim = returned := (Hstring.HMap.add n (t,dim) (!returned)) in
  let write_global (loc, name, var_type) =
    add_to_map name var_type 0;
    pfile "let %s = ref %s\n" (get_var_name name) (get_value_for_type var_type ty_defs)
  in
  let write_const (loc, name, var_type) = 
    add_to_map name var_type 0;
    pfile "let %s = ref %s\n" (get_var_name name) (get_value_for_type var_type ty_defs) (* Note : les const n'ont pas réellement besoin d'être des ref *)
  in
  let write_array (loc, name, (dim, var_type)) =
    add_to_map name var_type (List.length dim);
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
  let manage_satom satom =
    let union_list = ref [] in
    Hstring.HMap.iter (fun var_name (t,d) -> union_list := (Hstring.HSet.singleton var_name)::(!union_list)) g_vars;
    let find e = try List.find (fun s -> Hstring.HSet.mem e s) !(union_list) with Not_found -> Hstring.HSet.singleton e
    in (* Renvoie la clef du union_map contenant e : Soit c'est une clef; soit c'est la clef de l'ensemble qui le contient *)
    let union e1 e2 = 
      let s1 = find e1 in 
      let s2 = find e2 in 
      let sunion = Hstring.HSet.union s1 s2 in 
      union_list := List.filter (fun s -> (s <> s1) && (s <> s2)) (!union_list);
      union_list := sunion::(!union_list)
    in
    (* Union find *)
    let unionfind = function 
      | Comp(Elem(e1, _) , Eq, Elem(e2, _)) | Comp(Elem(e1,_), Eq, Access(e2,_)) | Comp(Access(e1,_), Eq, Elem(e2,_)) | Comp(Access(e1,_), Eq, Access(e2, _)) -> union e1 e2 
      | Comp(Elem(e1, _), Eq, Const(e2)) | Comp(Const(e2), Eq, Elem(e1,_)) -> union e1 (Hstring.make (mconst_to_string e2)) 
      | _ -> () (* assert false *) 
    in 
    SAtom.iter unionfind satom;
    let union_map = ref (IntMap.empty) in
    let find_head_in s = 
      let h = ref (Hstring.HSet.choose s) in
      let d = ref (get_var_dim (!h) g_vars) in
      Hstring.HSet.iter (fun v -> 
        let nd = get_var_dim v g_vars in
        if nd < !d then (d := nd; h := v)
      ) s;
      !h
    in 
    let sub_build set = 
      let head = find_head_in set in 
      let set_without_head = Hstring.HSet.filter (fun v -> v <> head) set in
      let hm = try IntMap.find (get_var_dim head g_vars) (!union_map) with Not_found -> Hstring.HMap.empty in
      union_map := IntMap.add (get_var_dim head g_vars) (Hstring.HMap.add head Hstring.HSet.empty hm) (!union_map);
      Hstring.HSet.iter 
      (
        fun v -> let dim = get_var_dim v g_vars in 
        let hm = try IntMap.find dim (!union_map) with Not_found -> Hstring.HMap.empty in
        let s = try Hstring.HMap.find head hm with Not_found -> Hstring.HSet.empty in 
          
        union_map := IntMap.add dim (Hstring.HMap.add head (Hstring.HSet.add v s) hm) (!union_map)
      ) 
      set_without_head
    in
    List.iter sub_build (!union_list);
    (* Print union_map *)

    IntMap.iter 
    (
      fun d m -> 
        printf "%d : " d; 
        Hstring.HMap.iter (
          fun h s -> 
            printf " (%s :" (Hstring.view h);
            Hstring.HSet.iter (
              fun v -> 
                printf " %s " (Hstring.view v))
        s;
            printf ")") m;
        printf "\n"
    )
    (!union_map);
    printf "\n";
    (* On a maintenant l'union_map, plus qu'a l'écrire. *)
    let print_dim dim hm = 
      (* Les variables a dimension négatives sont les constantes *)
      if dim >= 0 then
        (
        (* On écrit une boucle for si dim > 0 *)
        if dim > 0 then 
          pfile "%sfor tmp_%d = 0 to (get_nb_proc () - 1) do \n" (mult_string "\t" dim) (dim-1);
        let print_set head set =
          (* On initialise la tête si dim tête = dim *)
          let init_sign = if dim = 0 then ":=" else "<-" in
          let dim_head = get_var_dim head g_vars in 
          let init_head = (dim_head = dim) in 
        
          let tabstr = mult_string "\t" (dim+1) in
          let headstr = if dim_head >= 0 then sprintf "%s%s" (get_var_name head) (deplier_var dim_head) else get_constr_name head in 
          let headgetstr = if dim_head = 0 then "(!"^headstr^")" else headstr in
          if init_head then 
            (
              pfile "%s%s %s %s;\n" tabstr headstr init_sign (get_random_for_type (get_var_type head g_vars) ty_defs)
            );
          let tail_set v = 
            pfile "%s%s%s %s %s;\n" tabstr (get_var_name v) (deplier_var dim) init_sign headgetstr
          in
          Hstring.HSet.iter tail_set set
          (* On met toutes les valeurs de la queue égale a la valeur de la tête *)
        in 
        Hstring.HMap.iter print_set hm
      )
    in 
    
    IntMap.iter print_dim (!union_map);
    (* Utiliser to_rev_set pour faire les done *)

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

    (* Note : 
      Comme j'ai décidé d'utiliser des ref pour une écriture plus simple du fichier, et que les transitions cubicle sont une évolution d'état en simulatané, il faut d'abord créer le nouvel état puis l'appliquer.
      On store une hashtbl avec toutes les nouvelles valeurs : Clef : Nom de variable Value : Nom de la variable contenant la nouvelle valeur
    *)

    let updated = Hashtbl.create (Hstring.HMap.cardinal g_vars) in

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
      print_term g_vars t1;
      print_op op;
      print_term g_vars t2;
    | True -> pfile "true"
    | False -> pfile "false"
    | _ -> () (* TODO : If then else *)
    in
    let print_atom_and atom = print_atom atom; pfile " && " in
    pfile "\t";
    SAtom.iter print_atom_and trans_info.tr_reqs;
    pfile "true\n\n";

    (* écriture de la tête de ac_ *)
    pfile "let ac_%s args = \n" trans_name;
    write_args ();

    (* écriture des assignations de variables de ac_ *)

    (* On écrit des switch comme un dépliement de if_else pour simplifier. *)
    let print_switch swts = 
      let print_switch_sub last (satom, term) = 
        if not last then   
        begin
          pfile "if ";
          SAtom.iter (print_atom_and) satom;
          pfile "true then "
        end;
        print_term g_vars term;
        if not last then pfile " else "
      in
      let reved = List.rev swts in
      let last_swts = List.hd reved in
      let swts_list = List.rev (List.tl reved) in
      List.iter (print_switch_sub false) swts_list;
      print_switch_sub true last_swts;
      pfile "\n"
    in

    let write_assign (var_to_updt, new_value) =
      pfile "\tlet %s = " (get_updated_name var_to_updt);
      begin
      match new_value with
        | UTerm(t) -> print_term g_vars t 
        | UCase(swts) -> print_switch swts
      end ;
      pfile " in \n";
      Hashtbl.add updated (get_var_name var_to_updt) (get_updated_name var_to_updt)
    in
    List.iter write_assign trans_info.tr_assigns;

    (* écriture des assignations non déterministe de ac_ *)
    let write_nondet var_name =
      pfile "\tlet %s = %s in\n" (get_updated_name var_name) (get_random_for_type (get_var_type var_name g_vars) ty_defs);
      Hashtbl.add updated (get_var_name var_name) (get_updated_name var_name)
    in
    List.iter write_nondet trans_info.tr_nondets;

    (* écriture des update d'array de ac_ *)
    (* 
      Pareil que updated, mais a comme clef la dimension de l'array mis a jour, puis comme valeur une liste de paire (var_name, new_value) 
      Il serait ici beaucoup plus efficace d'utiliser une Map
    *)

    let updated_array = ref IntMap.empty in
    let add_updated_array dim var_name updated_name =
      updated_array :=
      try 
        let tab = IntMap.find dim (!updated_array) in 
        IntMap.add dim ((var_name, updated_name)::tab) (!updated_array)
      with Not_found -> IntMap.add dim [(var_name, updated_name)] (!updated_array)
    in
    let write_upd up =
      let dim = List.length up.up_arg in
      add_updated_array dim (get_var_name up.up_arr) (get_updated_name up.up_arr);
      pfile "\tlet %s = " (get_updated_name up.up_arr);
      List.iter (fun _ -> pfile "Array.make (get_nb_proc ()) (") up.up_arg;
      pfile "%s" (get_value_for_type (get_var_type up.up_arr g_vars) ty_defs);
      List.iter (fun _ -> pfile ")") up.up_arg;
      pfile (" in\n");
      let tabstrapp = mult_string "\t" ((List.length up.up_arg)+1) in
      List.iter (fun arg -> pfile "\tfor %s = 0 to ((get_nb_proc ()) - 1) do \n " (Hstring.view arg)) up.up_arg;
      pfile "%s%s%s <- " tabstrapp (get_updated_name up.up_arr) (deplier_var_list up.up_arg);
      print_switch up.up_swts;
      List.iter (fun arg -> pfile "\tdone; \n") up.up_arg; 
    in 
    List.iter write_upd trans_info.tr_upds;

    (* Application de la transition *)

    Hashtbl.iter (fun k v -> pfile "\t%s := %s;\n" k  v) updated;
    let app_upd k v =
      let tabstr = mult_string "\t" k in 
      let tabstrapp = tabstr^"\t" in
      pfile "%sfor tmp_%d = 0 to ((get_nb_proc ()) - 1) do \n" tabstr (k-1);
      List.iter 
      (
        fun (var_name, new_value) -> pfile "%s%s%s <- %s%s;\n" tabstrapp var_name (deplier_var k) new_value (deplier_var k); 
      ) 
      v
    in
    IntMap.iter app_upd (!updated_array);
    let max_card = IntMap.cardinal (!updated_array) in
    for i = 1 to max_card do pfile "%sdone;\n" (mult_string "\t" (max_card - i + 1)) done;
    
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
    pfile "\tadd_req_acc %s %s;\n" (string_of_int (List.length trans_info.tr_args)) trans_name
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
