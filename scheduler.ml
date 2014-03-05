open Options
open Ast
open Ast.Atom
open Format
open Random

type error = MustBeSingleNum

exception ETrue
exception EFalse

exception Error of error

let error e = raise (Error e)

type values = Int of int | Hstr of Hstring.t | Proc of int

let trans_list = ref []

let threads = 
  let rec buildlist i n =
    if i >= n then [] 
    else
      i::(buildlist (i+1) n)
  in
  buildlist 0 nb_threads

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
  with Not_found -> printf "Type not found error %a\t@." Hstring.print g_type; Hstr g_type

let value_c c =
  match MConst.is_num c with
    | Some e -> Num.int_of_num e
    | None -> error (MustBeSingleNum)

let value_t t =
  match t with
    | Const c -> Int (value_c c)
    | Elem (e, _) -> Hstr e
    (*| Access (arr, pl) -> 
      let arr = Hashtbl.find htbl_arrays arr in
      arr.(i) *)
    | _ -> assert false

let find_op =
  function
    | Eq -> (=)
    | Lt -> (<)
    | Le -> (<=)
    | Neq -> (<>)

(* PAS SUR DU TOUT *)
let find_value sub =
  function
    | Const c -> Int (value_c c)
    | Elem (id, Glob) -> 
      begin
	try Hashtbl.find htbl_globals id 
	with Not_found -> printf "Id not found %a@." Hstring.print id; exit 1
      end
    | Elem (id, Constr) -> Hstr id
    | Elem (id, _) -> let (_, i) = try
				     List.find (fun (e, _) -> Hstring.equal e id) sub 
      with Not_found -> printf "Sub not found -> %a@." Hstring.print id; exit 1
		      in
		      Proc i
    | Access (id, [ind]) -> 
      let (_, i) = try
		     List.find (fun (e, _) -> Hstring.equal e ind) sub 
	with Not_found -> printf "Sub not found -> %a@." Hstring.print id; exit 1
      in
      let array = 
	try
	  Hashtbl.find htbl_arrays id
	with Not_found -> printf "Array not found %a@." Hstring.print id; exit 1
      in
      array.(i)
    | _ -> assert false
      
let subst_req sub req =
  let f = fun () ->
    match req with
      | True -> raise ETrue
      | False -> raise EFalse
      | Comp (t1, op, t2) -> 
	let t1_value = find_value sub t1 in
	let t2_value = find_value sub t2 in
	begin 
	  match t1_value, t2_value with
	    | Int i1, Int i2 | Proc i1, Proc i2 -> 
	      let operator = find_op op in
	      operator i1 i2
	    | Hstr h1, Hstr h2 ->
	      begin
		match op with
		  | Eq -> Hstring.equal h1 h2
		  | Neq -> not (Hstring.equal h1 h2)
		  | _ -> assert false
	      end
	    | _ -> assert false
	end
      | _ -> assert false
  in f

(* Type : (unit -> bool) list list list
                         conj disj conj *)
let subst_ureq sub ureq =
  List.fold_left (
    (* forall_other z -> SAtom List *)
    fun conj_acc (_, sa_lst_ureq) ->
      let subst_satom =
	List.fold_left (
	  (* SAtom *)
	  fun disj_acc sa_ureq ->
	    let subst_satom_list =
	      SAtom.fold (
		(* Atom *)
		fun ureq conj_acc' ->
		  let subst_atom =
		    List.fold_left (
		      (* Each atom with all the substitutions *)
		      fun subst_atom s ->
			(subst_req s ureq)::subst_atom
		    ) [] sub
		  in subst_atom @ conj_acc'
	      ) sa_ureq []
	    in subst_satom_list :: disj_acc
	) [] sa_lst_ureq
      in subst_satom :: conj_acc
  ) [] ureq 

let substitute_guard sub reqs =
  try
    (* Existential requires management *)
    SAtom.fold (
      fun req acc ->
	let subst_req = subst_req sub req in
	subst_req::acc
    ) reqs [] 
  with ETrue -> [fun () -> true]
    
let substitute_updts sub assigns upds =
  sub

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
	    | Comp (t1, Eq, t2) ->
	      begin
		let value = match t2 with
		  | Elem (id2, _) -> Hstr id2
		  | Const c -> Int (value_c c)
		  | Access (id2, [i2]) -> failwith "TODO"
		  | _ -> assert false
		in
		match t1 with 
		  (* Init global variables *)
		  | Elem (id1, _) ->
		    Hashtbl.replace htbl_globals id1 value
		  (* Init arrays *)
		  | Access (id1, _) ->
		    let tbl = try
				Hashtbl.find htbl_arrays id1 
		      with Not_found -> printf "Array not found %a@." Hstring.print id1; exit 1 
		    in
		    Array.fill tbl 0 (Array.length tbl) value;
		    Hashtbl.replace htbl_arrays id1 tbl	
		  (* Should not occure *)
		  | _ -> assert false
	      end
	    | _ -> assert false
	      
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
      (* Associate the processes to numbers (unique) *)
      let substitutions = 
	if List.length tr.tr_args > List.length threads then [] 
	else Ast.all_permutations tr.tr_args threads
      in
      List.fold_left (
	fun acc' sub -> 
	  try 
	    let substitutions_msub = List.filter (fun e -> e <> sub) substitutions in
	    (*List.iter ( 
	      fun sub ->
		List.iter (
		  fun (h, i) -> printf "%a %d@." Hstring.print h i
		) sub
	    ) substitutions_msub;*)
	    let subst_ureq = subst_ureq substitutions_msub tr.tr_ureq in
	    let subst_guard = substitute_guard sub tr.tr_reqs in
	    let subst_updates = substitute_updts sub tr.tr_assigns tr.tr_upds in
	    (tr.tr_name, subst_guard, subst_ureq, subst_updates)::acc'
	  with EFalse -> acc'
      ) acc substitutions
  ) [] trans

(* SCHEDULING *)

let valid_req req =
  List.for_all (fun e -> e ()) req

let valid_ureq ureq = 
  List.for_all (
    fun fao ->
      List.exists (
	fun sal ->
	  List.for_all (
	    fun satom -> satom ()
	  ) sal
      ) fao
  ) ureq

let valid_trans_list () =
  let trans_list = !trans_list in
  List.fold_left (
    fun updts_l (name, req, ureq, updts) ->
      if valid_req req && valid_ureq ureq then (name, updts)::updts_l
      else updts_l
  ) [] trans_list

let random_transition () =
  let valid_trans = valid_trans_list () in
  let n = Random.int (List.length valid_trans) in
  let (name, updts) = List.nth valid_trans n in
  (*printf "%a\n" Hstring.print name;*)
  updts

let update_system () =
  let _ = random_transition () in
  ()
    

(* MAIN *)
    
let scheduler se =
  Random.self_init ();
  init_system se;
  init_transitions se.trans;
  update_system ()
