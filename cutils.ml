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

type g_varst = (Hstring.t * int) Hstring.HMap.t

let tmp_file_name = "simulator/stmp.ml"   (* Fichier sortie vers lequel le fichier cubicle va être compilé. Doit avoir un suffixe en ".ml" *)
let out_file = open_out tmp_file_name  
let var_prefix = "v"                      (* Préfixe pour les noms de variable. Nécéssaire car les variables cubicle commencent par une majuscule, impossible en caml *)
let updated_prefix = "n"                  (* Voir dans transition *)
let pfile = fun d -> fprintf out_file d

let get_var_type var_name g_vars    = let (t,_) = Hstring.HMap.find var_name g_vars in t
let get_var_dim  var_name  g_vars   = try let (_, d) = Hstring.HMap.find var_name g_vars in d with Not_found -> -1

(* BEGIN : Fonction d'aide ; Peut être a déplacer dans un fichier 'clib.ml' *)
let get_var_name v = sprintf "%s%s" var_prefix (Hstring.view v)
let get_updated_name v = sprintf "%s%s" updated_prefix (Hstring.view v)
let get_constr_name s g_vars =
  let sstring = Hstring.view s in match sstring with
    | "@MTrue" -> "true"
    | "@MFalse" -> "false"
    | _ -> 
        try ignore(int_of_string sstring); sstring    with Failure (_) ->
        try ignore(float_of_string sstring); sstring  with Failure (_) -> 
        try ignore(bool_of_string sstring); sstring   with Invalid_argument (_) ->
          "\""^sstring^"\""

(* Utilisé pour renvoyer une valeur d'initialisation quelconque avec le bon type pour une variable *)
let get_value_for_type ty ty_defs = 
  match (Hstring.view ty) with 
  | "int" | "proc" -> "0"
  | "real" -> "0."
  | "bool" | "mbool" -> "true"
  | _ -> "\""^Hstring.view (List.hd (Hashtbl.find ty_defs ty))^"\"" (* Note : Hashtbl.find ne devrait pas throw Not_Found car ast valide. *) 

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
      | hd::tl -> sprintf "%s%s%s" prev (Hstring.view hd) (sub_hsllts tl "; ")
  in 
  sprintf "[%s]" (sub_hsllts hsl "")

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
  | Elem(var, Constr) -> pfile "%s" (get_constr_name var g_vars)
  | Elem(var, Var)    -> pfile "%s" (Hstring.view var)
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
  | t -> Format.sprintf "get_random_in_list %s" t


module IntMap = Map.Make(struct type t = int let compare : int -> int -> int = Int.compare end) 

(* END : Fonction d'aide *)

