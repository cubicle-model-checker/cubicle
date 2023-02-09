open Ast
open Types
open Util
open Atom
open Printf
open Cutils

(*
  Quelques notes qui valent pour toutes les fonctions du fichier: 
  En général, les fonctions sont des séquences d'instruction.
  On écrit une instruction en considérant que il y a une autre instruction qui va suivre. 
  On l'écrit également en considérant qu'on est sur une nouvelle ligne. On va donc généralement finir les ligne par ';\n'.
  On va en genéral finir toutes les fonctions de type unit par "()". Si il n'y a aucune instruction avant, ça marchera quand même, et si il y en a ça permet d'avoir une instruction finale.
  C'est une solution beaucoup plus simple que de séparer les premières instruction de la dernière, créant un code pour le compilateur plus complexe.
*)

(* Type declaration *)

let write_types t_def =
  let returned = Hashtbl.create (List.length t_def) in 
  let print_type hs = pfile " ; \"%s\"" (Hstring.view hs) in
  let write_possible_type hstring_list = List.iter print_type hstring_list in
  let write_type (loc, (t_name, t_values)) = 
    pfile "let %s = [\"%s\"" (Hstring.view t_name) (Hstring.view (List.hd t_values));
    write_possible_type (List.tl t_values);
    pfile "] in\n";
    Hashtbl.add returned t_name t_values
  in
  List.iter write_type (List.tl t_def); (* On prend ici la tl de t_def car le premier élément est la définition d'un type @Mbool qu'on ne va pas utiliser*)
  pfile "\n";
  returned

(* Variables declaration *)

(* 
   Returns Hstring.HMap.t with: 
  - As a key, the name of globals 
  - As a value, the pair (var_type : Hstring.t * var_dimension : int)
*)
let write_vars s ty_defs=
  let returned = ref Hstring.HMap.empty in
  let add_to_map n t dim = returned := (Hstring.HMap.add n (t,dim) (!returned)) in
  let write_onedim (_, name, var_type) =
    add_to_map name var_type 0;
    pfile "let %s = ref %s in\n" (get_var_name name) (get_value_for_type var_type ty_defs)
  in
  let write_array (_, name, (dim, var_type)) =
    add_to_map name var_type (List.length dim);
    pfile "let %s = " (get_var_name name);
    List.iter (fun _ -> pfile "Array.make (get_nb_proc ()) (") dim;
    pfile "%s" (get_value_for_type var_type ty_defs);
    List.iter (fun _ -> pfile ")") dim;
    pfile " in\n"
  in
  List.iter write_onedim s.globals;
  List.iter write_onedim s.consts;
  List.iter write_array s.arrays;
  pfile "\n";
  !returned

(* State getter *)

let write_state_getter g_vars ty_defs = 
  pfile "let state_getter () = \n";
  pfile "let ret = ref StringMap.empty in \n";
  pfile "let add_to_ret n v = ret := StringMap.add n v (!ret) in \n";
  let add_var_to_state name (ty, dim) =
    pfile "add_to_ret \"%s\" " (Hstring.view name);
    let nt =
      match (Hstring.view ty) with
      | "int" | "proc"  -> "VInt"
      | "bool"| "mbool" -> "VBool"
      | "real"  -> "VFloat"
      | _       -> "VConstr"
    in
    begin match dim with
    | 0 -> pfile "(Val(%s(!%s)))" nt (get_var_name name)
    | 1 -> pfile "(Arr(List.map (fun x -> %s(x)) (Array.to_list %s)))" nt (get_var_name name)
    | _ -> pfile "(Mat(List.map (fun y -> List.map (fun x -> %s(x)) (Array.to_list y)) (Array.to_list %s)))" nt (get_var_name name)
    end;
    pfile ";\n"
  in
  Hstring.HMap.iter add_var_to_state g_vars;
  pfile "!ret\nin\n\n"

(* Init declaration *)

let write_init (vars, dnf) g_vars ty_defs =
  pfile "let init () = \n";
  let manage_satom satom =
    (* Note :
      While following functions and vars are named 'unionfind', the code isn't exactly an implementation of a union find. 
      It could rather be compared to a topological sorting algorithm. 
      It's goal is to manage dependency between different variables.
    *) 
    (* Union List is a list of set that will containt equivalence class for all globals. *)
    let union_list = ref [] in
    Hstring.HMap.iter (fun var_name (t,d) -> union_list := (Hstring.HSet.singleton var_name)::(!union_list)) g_vars;

    let find (e : Hstring.t) : Hstring.HSet.t = try List.find (fun s -> Hstring.HSet.mem e s) !(union_list) with Not_found -> Hstring.HSet.singleton e
    in 
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
      | Comp(Elem(e1, _), Eq, Const(e2)) | Comp(Const(e2), Eq, Elem(e1,_)) | Comp(Access(e1,_), Eq, Const(e2)) | Comp(Const(e2), Eq, Access(e1,_))-> union e1 (Hstring.make (mconst_to_string e2)) 
      | _ -> printf "CCompiler Warning : Unsupported atom type\n" (* Currently, the compiler can only manage equality in init *)
    in 
    SAtom.iter unionfind satom;
    (* 
       We now have an equivalence class for each global vars.
       We are going to try to find an 'head' for each class. 
       This head will be the lowest dimension var in the whole class. 
       As a reminder, constr have a dimension of -1, so they will be choosen as an head first if possible. 
    *) 
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

    (*
      Now that we have a correct union_map, we can print it.
    *)
    let print_dim dim hm = 
      if dim >= 0 then (* We don't want to do anything for constr, only for vars with a positive dim *)
        (
        (* On écrit une boucle for si dim > 0 *)
        if dim > 0 then 
          pfile "%sfor tmp_%d = 0 to (get_nb_proc () - 1) do \n" (mult_string "\t" dim) (dim-1);
        let print_set head set =
          (* 
            We will only init the head if dim head is equal to the current working dim. 
            The dim of the head can't be superior to the current working dim (Because the head is the lowest dim possible in the class) 
            If it's lower, it means that it has already been initialised.
          *)
          let init_sign   = if dim = 0 then ":=" else "<-" in
          let dim_head    = get_var_dim head g_vars in 
          let init_head   = (dim_head = dim) in 
        
          let tabstr      = mult_string "\t" (dim+1) in
          let headstr     = if dim_head >= 0 then sprintf "%s%s" (get_var_name head) (deplier_var dim_head) else get_constr_name head g_vars in 
          let headgetstr  = if dim_head = 0 then "(!"^headstr^")" else headstr in
          if init_head then 
            (
              pfile "%s%s %s %s;\n" tabstr headstr init_sign (get_random_for_type (get_var_type head g_vars) ty_defs)
            );
          (* When the head is set, we only need to set each value in the tail equal to the head value *)
          let tail_set v = 
            pfile "%s%s%s %s %s;\n" tabstr (get_var_name v) (deplier_var dim) init_sign headgetstr
          in
          Hstring.HSet.iter tail_set set
        in 
        Hstring.HMap.iter print_set hm
      )
    in 
    
    IntMap.iter print_dim (!union_map);
    let revdim = IntMap.to_rev_seq (!union_map) in 
    Seq.iter (fun (i,_) -> if i > 0 then pfile "%sdone;\n" (mult_string "\t" i)) revdim;
    in
  List.iter manage_satom dnf;
  
  pfile "\t()\nin\n\n"

(* Transition declratation *)
let write_transitions trans_list ty_defs g_vars =
  let write_transition trans =
    let trans_info = trans.tr_info in
    let trans_name = Hstring.view trans_info.tr_name in
    
    let trans_args = trans_info.tr_args in 
    let write_args () = (* Since we're going to declare the transition args twice (Once in the req and once in the ac), we make it a function *)
    begin 
      let count = ref 0 in
      let write_args arg = 
        begin 
          pfile "\tlet %s = List.nth args %d in\n" (Hstring.view arg) (!count);
          count := (!count) + 1; 
        end in
      List.iter write_args trans_args;
    end in

    (*  NOTE : Since we know how to get the new_val_name from a var_name, we could just use a Set instead of a Hashtbl *)

    let updated = Hashtbl.create (Hstring.HMap.cardinal g_vars) in

    (* Write Req *)
    pfile "let req_%s args = \n" trans_name;
    write_args ();
        
    let print_op = function 
    | Eq -> pfile " = "
    | Le -> pfile " <= "
    | Lt -> pfile " < "
    | Neq -> pfile " <> "
    in
    let rec print_atom = function
    | Comp(t1, op, t2) -> 
      print_term g_vars t1;
      print_op op;
      print_term g_vars t2;
    | True -> pfile "true"
    | False -> pfile "false"
    | Ite(satom, t1, t2) -> (* NOTE : As of writing, Ite aren't actually implemented in the transition, so this will effectively never happen *) 
        pfile "if (";
        SAtom.iter print_atom_and satom;
        pfile ")then (";
        print_atom t1;
        pfile") else (";
        print_atom t2;
        pfile ")"
    and print_atom_and atom = print_atom atom; pfile " && " in
    pfile "\t";
    SAtom.iter print_atom_and trans_info.tr_reqs;
    pfile "\n";
    (* Type tr_ureq : Variable.t * Ast.dnf *)
    let print_ureq (v, dnf) = 
      pfile "\t(forall_other (fun %s -> " (Hstring.view v);
      List.iter (SAtom.iter print_atom_and) dnf;
      pfile "true) ";
      pfile "args) && \n"; 
    in
    List.iter print_ureq trans_info.tr_ureq;
    pfile "\ttrue\nin\n\n";
    

    pfile "let ac_%s args = \n" trans_name;
    write_args ();

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

    (* Non determinist update. *)
    let write_nondet var_name =
      pfile "\tlet %s = %s in\n" (get_updated_name var_name) (get_random_for_type (get_var_type var_name g_vars) ty_defs);
      Hashtbl.add updated (get_var_name var_name) (get_updated_name var_name)
    in
    List.iter write_nondet trans_info.tr_nondets;

    (* Update of array *)
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
      let tabstrapp = mult_string "\t" ((List.length up.up_arg)+1) in (* Tab needed to application *)
      let depth = ref 0 in (* Depth is only used to correctly indent the compiled code *)
      List.iter (fun arg -> depth := (!depth) + 1; pfile "%sfor %s = 0 to ((get_nb_proc ()) - 1) do \n " (mult_string "\t" (!depth)) (Hstring.view arg)) up.up_arg;
      pfile "%s%s%s <- " tabstrapp (get_updated_name up.up_arr) (deplier_var_list up.up_arg);
      print_switch up.up_swts;
      List.iter (fun arg -> pfile "%sdone; \n" (mult_string "\t" (!depth)); depth := (!depth)-1) up.up_arg; 
    in 
    List.iter write_upd trans_info.tr_upds;

    (* Actually apply the transition, set the new value to all vars*)

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
    
    pfile "\t()\nin\n";

    (* Create the transition to be able to add it to the transition table *)
    pfile "\nlet %s = (\"%s\", req_%s, ac_%s) \nin\n\n" trans_name trans_name trans_name trans_name
    in
  List.iter write_transition trans_list;

  (* Now that all transition have been created, we create a table storing all information about them to actually use them in the simulation *) 

  pfile "\nlet mymodel = ref Model.empty in\n\n";

  let write_table trans = 
    let trans_info = trans.tr_info in
    let trans_name = Hstring.view trans_info.tr_name in
    pfile "mymodel := Model.add_trans %s %s (!mymodel);\n" (string_of_int (List.length trans_info.tr_args)) trans_name
  in
  List.iter write_table trans_list;
  pfile "mymodel := Model.set_init init (!mymodel);\n";
  pfile "mymodel := Model.set_vars ([], state_getter) (!mymodel);\n";
  pfile "set_model (!mymodel)\n"

let write_unsafe unsafe =
  let sub_write_unsafe (_, vars, satom) = ()
  in List.iter sub_write_unsafe unsafe

let run ts s =
  pfile "open Utils\n";
  pfile "open Model\n";
  pfile "open Format\n\n";
  pfile "let build_model () =\n";
  let g_types = write_types s.type_defs in
  let g_vars = write_vars s g_types in
  write_state_getter g_vars g_types;
  write_init ts.t_init g_vars g_types;
  write_transitions ts.t_trans g_types g_vars;
  write_unsafe s.unsafe;
  close_out out_file;
  exit 0
