open Ast
open Ast.Atom
open Format

type error = MustBeSingleNum

exception Error of error

let error e = raise (Error e)

(* GLOBAL VARIABLES *)

(* TODO : This variable must be a parameter of the program *)
let nb_process = 4

(* Idea : We keep the visited transitions and their fathers *)
let (htbl_visited_transitions : (Hstring.t, Hstring.t list) Hashtbl.t) = Hashtbl.create 17

(* Types *)
let htbl_types = Hashtbl.create 11
let () = List.iter (
  fun (constr, fields) -> 
    Hashtbl.add htbl_types constr fields
) [ Hstring.make "proc", [Hstring.make "1"];
    Hstring.make "bool", [Hstring.make "False"];
    Hstring.make "int", [Hstring.make "0"]
  ]

(* Global variables with their value *)
let (htbl_globals : (Hstring.t, Hstring.t) Hashtbl.t) = Hashtbl.create 17

(* Hashtbl : name tbl -> tbl, indexes : process number *)
let (htbl_arrays : (Hstring.t, Hstring.t array) Hashtbl.t) = Hashtbl.create 17

(* DISPLAY METHODS *)
let display_system () =
  Hashtbl.iter (
    fun id value -> 
      printf "%a@." (Hstring.print_list "\t") [id; value]
  ) htbl_globals;
  Hashtbl.iter (
    fun id array -> 
      printf "%a\t" Hstring.print id;
      Array.iteri (
	fun i el -> 
	  printf "%a " (Hstring.print_list " ") [Hstring.make (string_of_int i); el]
      ) array;
      printf "@."
  ) htbl_arrays

(* USEFUL METHODS *)

let default_type g_type =
  try
    match Hashtbl.find htbl_types g_type with
      | [] -> g_type
      | hd::_ -> hd
  with Not_found -> printf "error %a\t" Hstring.print g_type; g_type

let value_c c =
  match MConst.is_num c with
    | Some e -> Hstring.make (Num.string_of_num e)
    | None -> error (MustBeSingleNum)

(* INITIALIZATION *)

let init_types type_defs =
  List.iter (
    fun (t_name, t_fields) ->
      Hashtbl.add htbl_types t_name t_fields
  ) type_defs

let init_globals globals =
  List.iter (
    fun (g_name, g_type) ->
      let default_type = default_type g_type in
      Hashtbl.add htbl_globals g_name default_type
  ) globals

let init_arrays arrays =
  List.iter (
    fun (a_name, (a_dims, a_type)) ->
      let dims = List.length a_dims in
      let default_type = default_type a_type in
      let new_t = Array.make (nb_process * dims) default_type in
      Hashtbl.add htbl_arrays a_name new_t
  ) arrays
    
let rec fill_system (vars, atoms) =
  List.iter (
    fun satom ->
      SAtom.iter (
	fun atom ->
	  match atom with 
	    (* Init global variables *)
	    | Comp (Elem (id1, _), Eq, term) ->
	      let value = match term with
		| Elem (id2, _) -> id2
		| Const c -> value_c c
		| Access (id2, [i2]) -> failwith "TODO"
		| _ -> assert false
	      in
	      Hashtbl.replace htbl_globals id1 value
		
	    (* Init arrays *)
	    | Comp (Access (id1, _), Eq, term) ->
	      let value = match term with
		| Elem (id2, _) -> id2
		| Const c -> value_c c
		| Access (id2, [i2]) -> failwith "TODO"
		| _ -> assert false
	      in 
	      let tbl = Hashtbl.find htbl_arrays id1 in
	      Array.fill tbl 0 (Array.length tbl) value;
	      Hashtbl.replace htbl_arrays id1 tbl
	    (* Should not occure *)
	    | _ -> printf "TODO\n@."
      ) satom
  ) atoms

let init_system se =
  init_types se.type_defs;
  init_arrays se.arrays;
  init_globals se.globals;
  fill_system se.init;
  display_system ()

(* SCHEDULING *)
