open Options
open Ast
open Ast.Atom
open Format
open Random

type error = MustBeSingleNum

exception Error of error

let error e = raise (Error e)

type values = Int of int | Hstr of Hstring.t | Proc of int

let trans_list = ref []

let threads = 
  let rec buildlist i n =
    if i > n then [] 
    else
      i::(buildlist (i+1) n)
  in
  buildlist 1 nb_threads

(* GLOBAL VARIABLES *)

(* Idea : We keep the visited transitions and their fathers *)
let (htbl_visited_transitions : (Hstring.t, Hstring.t list) Hashtbl.t) = Hashtbl.create 17

(* Types *)
let htbl_types = Hashtbl.create 11
let () = List.iter (
  fun (constr, fields) -> 
    Hashtbl.add htbl_types constr fields
) [ Hstring.make "proc", [Proc 1];
    Hstring.make "bool", [Hstr Ast.hfalse];
    Hstring.make "int", [Int 0]
  ]

(* Global variables with their value *)
let (htbl_globals : (Hstring.t, values) Hashtbl.t) = Hashtbl.create 17

(* Hashtbl : name tbl -> tbl, indexes : process number *)
let (htbl_arrays : (Hstring.t, values array) Hashtbl.t) = Hashtbl.create 17

(* USEFUL METHODS *)

let default_type g_type =
  try
    match Hashtbl.find htbl_types g_type with
      | [] -> Hstr g_type
      | hd::_ -> hd
  with Not_found -> printf "error %a\t@." Hstring.print g_type; Hstr g_type

let value_c c =
  match MConst.is_num c with
    | Some e -> Num.int_of_num e
    | None -> error (MustBeSingleNum)

let value_t ?ind:(i=0) t =
  match t with
    | Const c -> Int (value_c c)
    | Elem (e, _) -> Hstr e
    | Access (arr, pl) -> 
      let arr = Hashtbl.find htbl_arrays arr in
      arr.(i)
    | _ -> assert false

let array_exists p arr =
  try
    for i = 0 to Array.length arr - 1 do
      if p arr.(i) then raise Exit
    done; false
  with Exit -> true

let subst_guard p reqs ureq =
  p

let subst_updates p assigns upds =
  p


(* INITIALIZATION *)

let init_types type_defs =
  List.iter (
    fun (t_name, t_fields) ->
      let fields = List.fold_left (fun acc field -> acc@[Hstr field]) [] t_fields in
      Hashtbl.add htbl_types t_name fields
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
      let new_t = Array.make (nb_threads * dims) default_type in
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
		| Elem (id2, _) -> Hstr id2
		| Const c -> Int (value_c c)
		| Access (id2, [i2]) -> failwith "TODO"
		| _ -> assert false
	      in
	      Hashtbl.replace htbl_globals id1 value
		
	    (* Init arrays *)
	    | Comp (Access (id1, _), Eq, term) ->
	      let value = match term with
		| Elem (id2, _) -> Hstr id2
		| Const c -> Int (value_c c)
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
  fill_system se.init

let init_transitions trans =
  trans_list := List.fold_left (
    fun acc tr ->
      let permutations = 
	if List.length tr.tr_args > List.length threads then [] 
	else Ast.all_permutations tr.tr_args threads
      in
      List.fold_left (
	fun acc' p -> let s_guard = subst_guard p tr.tr_reqs tr.tr_ureq in
		      let s_updts = subst_updates p tr.tr_assigns tr.tr_upds in
		      (tr.tr_name, s_guard, s_updts)::acc'
      ) acc permutations
  ) [] trans

(* SCHEDULING *)

let find_op op =
  match op with
    | Eq -> (=)
    | Lt -> (<)
    | Le -> (<=)
    | Neq -> (<>)
    
let compare_to_elem op t2 t1v =
  let t2v = value_t t2 in
  match t1v, t2v with
    | Int v1, Int v2 | Proc v1, Proc v2 ->
      let operator = find_op op in
      operator v1 v2
    | Hstr h1, Hstr h2 ->
      begin
	let hequal = Hstring.equal h1 h2 in
	match op with
	  | Eq -> hequal
	  | Neq -> not hequal
	  | _ -> assert false
      end
    | _ -> assert false

let compare_to_array op t2 t1v =
  assert false



let valid_transition acc t =
  if SAtom.for_all (
    fun req -> match req with
      | Comp (t1, op, t2) -> 
	let compare =
	  match t2 with
	    | Access (_, _) -> compare_to_array
	    | Const _ -> compare_to_elem
	    | _ -> assert false
	in
	begin
	  match t1 with
	    (* Elem *)
	    | Elem (ht1, _) -> let t1v = Hashtbl.find htbl_globals ht1 in
		       compare op t2 t1v
	    (* Array *)
	    | Access (name, _) -> let array = Hashtbl.find htbl_arrays name in
			 array_exists (compare op t2) array
	    | _ -> assert false
	end
      | _ -> assert false
  ) t.tr_reqs then t::acc
  else acc

let transition_list se_trans =
  let valid_trans = List.fold_left valid_transition [] se_trans in
  (*List.iter (fun t -> printf "%a\n" Hstring.print t.tr_name) valid_trans;*)
  valid_trans

let random_transition se_trans =
  let valid_trans = transition_list se_trans in
  let n = Random.int (List.length valid_trans) in
  let trans = List.nth valid_trans n in
  printf "%a\n" Hstring.print trans.tr_name;
  trans

let update_system se_trans =
  let trans = random_transition se_trans in
  ()
  

(* MAIN *)
    
let scheduler se =
  Random.self_init ();
  init_system se;
  init_transitions se.trans;
  List.iter (
    fun (n, p, _) ->
      printf "%a : " Hstring.print n;
      List.iter (
	fun (hst, i) -> printf "%a %d\n@." Hstring.print hst i
      ) p
  ) !trans_list
