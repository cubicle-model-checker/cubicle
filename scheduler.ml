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

type value = 
  | Int of int 
  | Hstr of Hstring.t 
  | Proc of int

(* List of processes *)
let list_threads = 
  let rec lthreads l =
    function
      | n when n = nb_threads -> l
      | n -> n::(lthreads l (n+1))
  in lthreads [] 0

(* This list will contain all the transitions *)
let trans_list = ref []

(* Module to manage multi-dimensional arrays *)
module DimArray : sig
    
  type 'a t = 
    | Arr of 'a array 
    | Mat of 'a t array

  type 'a dimt = {dim:int; darr:'a t}
      
  val init : int -> int -> 'a -> 'a dimt
  val get : 'a dimt -> int list -> 'a
  val set : 'a dimt -> int list -> 'a -> unit
  val print : 'a dimt ->  (Format.formatter -> 'a -> unit) -> unit
    
end = struct
    
  type 'a t = 
    | Arr of 'a array 
    | Mat of 'a t array

  type 'a dimt = {dim:int; darr:'a t}

  let init d nb_elem v =
    let darr = 
      let rec init' d nb_elem v =
	match d with
	  | 1 -> Arr (Array.init nb_elem (fun _ -> v))
	  | n -> Mat (Array.init nb_elem (fun _ -> (init' (n-1) nb_elem v)))
      in init' d nb_elem v
    in {dim=d; darr=darr}

  let get t ind = 
    let rec get' t ind =
      match t, ind with 
	| Arr a, [i] -> a.(i) 
	| Mat m, hd::tl -> let t = m.(hd) in get' t tl 
	| _ -> failwith "Index error in Arr module, get"
    in get' t.darr ind

  let set t ind v =
    let rec set' t ind =
      match t, ind with
	| Arr a, [i] -> a.(i) <- v
	| Mat m, hd::tl -> let t = m.(hd) in set' t tl
	| _ -> failwith "Index error in Arr module, set"
    in set' t.darr ind

  let print t p =
    let rec print' t =
      match t with
	| Arr a -> printf "[| "; Array.iter (fun e -> printf " %a |" p e) a; printf "]"
	| Mat m -> Array.iter (fun e -> print' e; printf "@.") m
    in print' t.darr

end




(* GLOBAL VARIABLES *)


(* Global variables with their value *)
let (htbl_globals : (Hstring.t, value) Hashtbl.t) = Hashtbl.create 17

(* Hashtbl : name tbl -> tbl, indexes : process number *)
let (htbl_arrays : (Hstring.t, value DimArray.dimt) Hashtbl.t) = Hashtbl.create 17

(* Types *)
let htbl_types = Hashtbl.create 11

(* Filling htbl_types with default types (proc, bool and int) *)
let () = 
  List.iter (
    fun (constr, fields) -> 
      Hashtbl.add htbl_types constr fields
  ) [ Hstring.make "proc", List.map (fun i -> Proc i) list_threads;
      Hstring.make "bool", [Hstr Ast.hfalse; Hstr Ast.htrue];
      Hstring.make "int", [Int 0]
    ]

(* USEFUL METHODS *)


(* Tranform a constant in an int *)
let value_c c =
  match MConst.is_num c with
    | Some e -> Num.int_of_num e
    | None -> error (MustBeSingleNum)

(* Operators on int and real *)
let find_op =
  function
    | Eq -> (=)
    | Lt -> (<)
    | Le -> (<=)
    | Neq -> (<>)

(* Return the first type constructor *)
let default_type g_type =
  match Hashtbl.find htbl_types g_type with
    | [] -> Hstr g_type
    | hd::_ -> hd

(* Intersection of two lists *)
let inter l1 l2s =
  let l1s = List.sort Pervasives.compare l1 in
  (* l2s is already sorted *)
  let rec inter' l1 l2 =
    match l1, l2 with
      | [], _ -> l2
      | _, [] -> l1
      | hd1::tl1, hd2::tl2 when hd1 = hd2 -> inter' tl1 tl2
      | hd1::tl1, hd2::_ when hd1 < hd2 -> let l' = inter' tl1 l2 in
					   hd1::l'
      | _, hd2::tl2 -> let l' = inter' l1 tl2 in
		       hd2::l'
  in inter' l1s l2s



(* VALUE METHODS *)


let get_value sub =
  function
    | Const c -> Int (value_c c)
    | Elem (id, Glob) -> Hashtbl.find htbl_globals id
    | Elem (id, Constr) -> Hstr id
    | Elem (id, _) -> let (_, i) = 
			List.find (fun (e, _) -> Hstring.equal e id) sub 
		      in Proc i
    | Access (id, pl) -> 
      let ind = List.map (
	fun p -> 
	  let (_, i) = List.find (
	    fun (p', _) -> p = p'
	  ) sub in i
      ) pl in
      let tab = Hashtbl.find htbl_arrays id in
      DimArray.get tab ind
    | _ -> assert false


let print_value f v =
  match v with
    | Int i -> printf "Int %d" i
    | Proc p -> printf "Proc %d" p
    | Hstr h -> printf "Hstr %a" Hstring.print h




(* SUBSTITUTION METHODS *)

      
(* Here, optimization needed if constant values *)     
let subst_req sub req =
  let f = fun () ->
    match req with
      | True -> raise ETrue
      | False -> raise EFalse
      | Comp (t1, op, t2) -> 
	let t1_value = get_value sub t1 in
	let t2_value = get_value sub t2 in
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
	    (* Problem with ref_count.cub, assertion failure *)
	    | _ -> assert false
	end
      | _ -> assert false
  in f

(* Type : (unit -> bool) list list list
   ____ (fun () -> bool) conj disj conj *)
let subst_ureq subst subsm ureq =
  List.fold_left (
    (* Conjonction of forall_other z -> SAtom List *)
    fun conj_acc (k, sa_lst_ureq) ->
      let subst_satom =
	List.fold_left (
	  (* Disjonction of SAtom *)
	  fun disj_acc sa_ureq ->
	    let subst_satom_list =
	      SAtom.fold (
		(* Conjonction of Atom *)
		fun ureq conj_acc' ->
		  let subst_atom =
		    List.fold_left (
		      (* Conjonction of substitute Atom *)
		      fun subst_atom s ->
			let sub = (k, s) in
			(subst_req (sub::subst) ureq)::subst_atom
		    ) [] subsm
		  in subst_atom @ conj_acc'
	      ) sa_ureq []
	    in subst_satom_list :: disj_acc
	) [] sa_lst_ureq
      in subst_satom :: conj_acc
  ) [] ureq 

let substitute_req sub reqs =
  (* Existential requires management *)
  SAtom.fold (
    fun req acc ->
      try
	let subst_req = subst_req sub req in
	subst_req::acc
      with ETrue -> acc
  ) reqs [] 

let substitute_updts sub assigns upds =
  let subst_assigns = List.fold_left (
    fun acc (var, assign) -> 
      (fun () -> let value = get_value sub assign in
		 Hashtbl.replace htbl_globals var value)::acc
  ) [] assigns in
  let subst_upds = List.fold_left (
    fun tab_acc u -> 
      let arr = Hashtbl.find htbl_arrays u.up_arr in
      let arg = u.up_arg in
      let subs = Ast.all_permutations arg list_threads in
      let upd_tab =
	List.fold_left (
	  fun upd_acc spl ->
	    let s = spl@sub in
	    let (_, pl) = List.split spl in
	    let supd =
	      List.fold_right (
		fun (conds, term) disj_acc ->
		  let filter =
		    SAtom.fold (
		      fun cond conj_acc -> (subst_req s cond)::conj_acc
		    ) conds [] in 
		  let t = get_value s term in
		  let f = fun () ->
		    DimArray.set arr pl t;
		    Hashtbl.replace htbl_arrays u.up_arr arr
		  in
		  (filter, f)::disj_acc
	      ) u.up_swts []
	    in supd::upd_acc
	) [] subs
      in upd_tab::tab_acc
  ) [] upds in
  (subst_assigns, subst_upds)
				    
(*
	    printf "%a :@." Hstring.print u.up_arr;
	    let arr = Hashtbl.find htbl_arrays u.up_arr in
       	    List.iter (
	      fun (cond, t) ->
		print_satom cond;
		match t with
		  | Const i -> printf "%d@." (value_c i)
		  | Elem (h, _) -> printf "%a@." Hstring.print h
		  | Access (n, pl) -> printf "%a [%a]@." Hstring.print n (Hstring.print_list " ") pl
		  | _ -> assert false
	    ) u.up_swts;
	    printf "end %a@." Hstring.print u.up_arr
*)


(* INITIALIZATION *)


(* Each type is associated to his constructors 
   The first one is considered as the default type *)
let init_types type_defs =
  List.iter (
    fun (t_name, t_fields) ->
      let fields = List.fold_right (
	fun field acc -> (Hstr field)::acc
      ) t_fields [] in
      Hashtbl.add htbl_types t_name fields
  ) type_defs

(* Initialization of the global variables to their
   default constructor. *)
let init_globals globals =
  List.iter (
    fun (g_name, g_type) ->
      let default_type = default_type g_type in
      Hashtbl.add htbl_globals g_name default_type
  ) globals

(* Initialization of the arrays with their default
   constructor (deterministic version) *)
let init_arrays arrays =
  List.iter (
    fun (a_name, (a_dims, a_type)) ->
      let dims = List.length a_dims in
      (* Here is the deterministic initialization *)
      let default_type = default_type a_type in
      let new_t = DimArray.init dims nb_threads default_type in
      (* End of the deterministic initialization *)
      Hashtbl.add htbl_arrays a_name new_t
  ) arrays
    
(* Execution of the real init method from the cubicle file *)
let rec initialization (vars, atoms) =
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
		  | Access (id1, pl) -> 
		    let tbl = DimArray.init (List.length pl) nb_threads value in
		    (*DimArray.print tbl print_value;
		      printf "\n@.";
		    *)Hashtbl.replace htbl_arrays id1 tbl	
		  (* Should not occure *)
		  | _ -> assert false
	      end
	    | _ -> assert false
	      
      ) satom
  ) atoms

let init_system se =
  init_types se.type_defs;
  (* This part may change, deterministic for now *)
  init_arrays se.arrays;
  init_globals se.globals;
  (* --- After this, all the variables and arrays are initialized --- *)
  initialization se.init

let init_transitions trans =
  trans_list := List.fold_left (
    fun acc tr ->
      (* Associate the processes to numbers (unique) *)
      let subs = 
	if List.length tr.tr_args > nb_threads 
	then [] (* Should not occure *)
	else Ast.all_permutations tr.tr_args list_threads
      in
      List.fold_left (
	fun acc' sub -> 
	  try 
	    let (_, pl) = List.split sub in
	    let subsm = inter pl list_threads in
	    let subst_ureq = subst_ureq sub subsm tr.tr_ureq in
	    let subst_guard = substitute_req sub tr.tr_reqs in
	    let subst_updates = substitute_updts sub tr.tr_assigns tr.tr_upds in
	    let tr_name = ref (Hstring.view tr.tr_name) in
	    List.iter (fun (id, i) -> let si = string_of_int i in
				      tr_name := !tr_name ^ " " ^ (Hstring.view id) ^ si;) sub;
	    (Hstring.make !tr_name, subst_guard, subst_ureq, subst_updates)::acc'
	  with EFalse -> acc'
      ) acc subs
  ) [] trans



(* SCHEDULING *)


let valid_req req =
  List.for_all (fun e -> e ()) req

let valid_ureq ureq = 
  List.for_all (
    fun for_all_other ->
      List.exists (
	fun s_atom_funs_list ->
	  List.for_all (
	    fun s_atom_funs -> s_atom_funs ()
	  ) s_atom_funs_list
      ) for_all_other
  ) ureq

let valid_upd arrs_upd =
  List.fold_left (
    fun arr_acc arr_upds ->
      let arrs_u = 
	List.fold_left (
	  fun acc elem ->
	    let (_, upd) = List.find (
	      fun (cond, _) -> List.for_all (fun c -> c ()
	      ) cond
	    ) elem in
	    upd::acc
	) [] arr_upds
      in arrs_u::arr_acc
  ) [] arrs_upd

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
  printf "Tr : %a\n" Hstring.print name;
  updts



(* SYSTEM UPDATE *)


let print_globals () =
  printf "@.";
  Hashtbl.iter (
    fun var value ->
      printf "%a -> " Hstring.print var;
      match value with
	| Int i -> printf "i %d@." i
	| Proc i -> printf "p %d@." i
	| Hstr h -> printf "h %a@." Hstring.print h
  ) htbl_globals;
  Hashtbl.iter (
    fun name tbl -> printf "%a " Hstring.print name;
      DimArray.print tbl print_value;
      printf "@."
  ) htbl_arrays;
  printf "\n@."

let update_system () =
  print_globals ();
  let (assigns, updates) = random_transition () in
  List.iter (fun a -> a ()) assigns;
  let updts = valid_upd updates in List.iter (fun us -> List.iter (fun u -> u ()) us )  updts;
  print_globals ();
  let (assigns, updates) = random_transition () in
  List.iter (fun a -> a ()) assigns;
  let updts = valid_upd updates in List.iter (fun us -> List.iter (fun u -> u ()) us )  updts;
  print_globals ();
  let (assigns, updates) = random_transition () in
  List.iter (fun a -> a ()) assigns;
  let updts = valid_upd updates in List.iter (fun us -> List.iter (fun u -> u ()) us )  updts;
  print_globals ()
    



(* MAIN *)

    
let scheduler se =
  Random.self_init ();
  init_system se;
  init_transitions se.trans;
  update_system ()
