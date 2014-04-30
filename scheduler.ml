open Options
open Ast
open Ast.Atom
open Format
open Random
open Num
open Lexing

type error = MustBeSingleNum

exception ETrue
exception EFalse
exception Inversion
exception ConstrRep

exception Error of error

let report (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  printf "File \"%s\", line %d, characters %d-%d:" file l fc lc

let () =
  let cin = match ofile with
    | Some s -> open_in ((Filename.chop_extension s)^".sched")
    | None -> assert false
  in
  let lb = Lexing.from_channel cin in
  try 
    Parser.scheduler Lexer.token lb
  with 
      Parsing.Parse_error ->
	let  loc = (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb) in
	report loc;
        printf "\nsyntax error\n@.";
	exit 2
	  
let init_proc = !init_proc

let error e = raise (Error e)

type value = 
  | Var of Hstring.t
  | Numb of num
  | Hstr of Hstring.t 
  | Proc of int

type stype =
  | RGlob of Hstring.t
  | RArr of (Hstring.t * int)

type ty =
  | A (* abstract type *)
  | N (* int or real *)
  | O (* everything else *)

let fproc = ref (Proc 0)

(* List of processes *)
let list_threads = 
  let rec lthreads l =
    function
      | n when n = nb_threads -> fproc := Proc n; l
      | n -> n::(lthreads l (n+1))
  in lthreads [] 0

(* This list will contain all the transitions *)
let trans_list = ref []

(* Module to manage multi-dimensional arrays *)
module type DA = sig
    
  type 'a t
    
  type 'a dima

  val init : int -> int -> 'a -> 'a dima
  val minit : int -> int -> ('a * int) list -> 'a -> 'a dima
  val get : 'a dima -> int list -> 'a
  val set : 'a dima -> int list -> 'a -> unit
  val print : 'a dima -> (Format.formatter -> 'a -> unit) -> unit
  val copy : 'a dima -> 'a dima
  val dim : 'a dima -> int
    
end 

module DimArray : DA = struct
    
  type 'a t = 
    | Arr of 'a array 
    | Mat of 'a t array

  type 'a dima = {dim:int; darr:'a t}

  let init d nb_elem v =
    let darr = 
      let rec init' d =
	match d with
	  | 1 -> Arr (Array.init nb_elem (fun _ -> v))
	  | n -> Mat (Array.init nb_elem (fun _ -> init' (n-1)))
      in init' d
    in {dim=d; darr=darr}

  let minit d nb_elem al v =
    let darr = 
      let rec init' d =
	match d with
	  | 1 -> let a = Array.init nb_elem (fun _ -> v) in
		 let i = ref 0 in
		 List.iter (
		   fun (c, n) ->
		     for j = !i to n - 1 do
		       a.(j) <- c
		     done;
		     i := !i + n - 1
		 ) al;
		 Arr a
	  | n -> Mat (Array.init nb_elem (fun _ -> init' (n-1)))
      in init' d
    in {dim=d; darr=darr}
    
  let get t ind = 
    let rec get' t ind =
      match t, ind with 
	| Arr a, [i] -> a.(i) 
	| Mat m, hd::tl -> let t = m.(hd) in get' t tl 
	| _ -> failwith "DimArray.get : Index error"
    in get' t.darr ind

  let set t ind v =
    let rec set' t ind =
      match t, ind with
	| Arr a, [i] -> a.(i) <- v
	| Mat m, hd::tl -> let t = m.(hd) in set' t tl
	| _ -> failwith "DimArray.set : Index error"
    in set' t.darr ind

  let print t f =
    let rec print' t =
      match t with
	| Arr a -> printf "[| ";
	  Array.iter (fun e -> printf "%a " f e) a;
	  printf "|]"
	| Mat m -> printf "[| ";
	  Array.iter (fun a -> print' a) m;
	  printf "|]"
    in print' t.darr

  let copy t =
    let rec copy' t =
      match t with
	| Arr a -> Arr (Array.copy a)
	| Mat m -> Mat (Array.map (fun a -> copy' a) m)
    in {dim = t.dim; darr = copy' t.darr}

  let dim t = t.dim

end

module type St = sig

  (* A dimensional array *)
  type 'a da
  (* The state : global variables and arrays *)
  type 'a t = {globs :(Hstring.t, 'a) Hashtbl.t; arrs : (Hstring.t, 'a da) Hashtbl.t}
      
  val init : unit -> 'a t
    
  val equal : 'a t -> 'a t -> bool
  val hash : 'a t -> int
    
  (* Get a global variable value *)
  val get_v : 'a t -> Hstring.t -> 'a
  (* Get an array by its name *)
  val get_a : 'a t -> Hstring.t -> 'a da
  (* Get an element in an array by its name and a a param list*)
  val get_e : 'a t -> Hstring.t -> int list -> 'a
    
  (* Set a global variable value *)
  val set_v : 'a t -> Hstring.t -> 'a -> unit
  (* Set an array by its name and a new array *)
  val set_a : 'a t -> Hstring.t -> 'a da -> unit
  (* Set an element in an array by its name, a param list and a value *)
  val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
    
  val copy : 'a t -> 'a t

  val clear : 'a t -> unit
    
end

module State ( A : DA ) : St with type 'a da = 'a A.dima = struct
    
  type 'a t = {globs: (Hstring.t, 'a) Hashtbl.t; arrs: (Hstring.t, 'a A.dima) Hashtbl.t}
  type 'a da = 'a A.dima

  let init () = {globs = Hashtbl.create 17; arrs = Hashtbl.create 17}

  let equal s1 s2 =
    try
      let gs1 = s1.globs in
      let gs2 = s2.globs in
      Hashtbl.iter (
	fun g v1 -> let v2 = Hashtbl.find gs2 g in
		    if v1 <> v2 then raise Exit
      ) gs1;
      true
    with
	Exit -> false

  let hash = Hashtbl.hash

  let get_v t h = Hashtbl.find t.globs h
  let get_a t h = Hashtbl.find t.arrs h
  let get_e t h pl = let arr = get_a t h in
		     A.get arr pl

  let set_v t h v = Hashtbl.replace t.globs h v
  let set_a t h arr = Hashtbl.replace t.arrs h arr
  let set_e t h pl v = let arr = get_a t h in
		       A.set arr pl v

  let copy t = let carrs = Hashtbl.copy t.arrs in
	       Hashtbl.iter (fun name arr -> Hashtbl.replace carrs name (A.copy arr)) carrs;
	       {globs = Hashtbl.copy t.globs; arrs = carrs}

  let clear t = Hashtbl.clear t.globs;
    Hashtbl.clear t.arrs

end


module type Sys = sig

  (* A state *)
  type 'a s
  (* A dimensional array *)
  type 'a da
  type 'a set
  (* A record with a readable state and a writable state *)
  type 'a t = {syst : 'a set; init : 'a set; read_st : 'a s; write_st : 'a s}

  val init : unit -> 'a t

  val get_v : 'a t -> Hstring.t -> 'a
  val get_a : 'a t -> Hstring.t -> 'a da
  val get_e : 'a t -> Hstring.t -> int list -> 'a

  val set_v : 'a t -> Hstring.t -> 'a -> unit
  val set_a : 'a t -> Hstring.t -> 'a da -> unit
  val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit

  val exists : ('a s -> bool) -> 'a set -> bool
    
  val update_init : 'a t -> (Hstring.t * 'a s) -> 'a t

  val get_init : 'a t -> 'a set

  val new_init : Hstring.t -> 'a t -> 'a s -> 'a t

  val update_s : Hstring.t -> 'a t -> 'a t
    
end

module System ( S : St ) : Sys 
  with type 'a da = 'a S.da and type 'a s = 'a S.t and type 'a set = (Hstring.t * 'a S.t) list = struct

    type 'a da = 'a S.da
    type 'a s = 'a S.t
    type 'a set = (Hstring.t * 'a S.t) list
    type 'a t = {syst : (Hstring.t *'a S.t) list; init : (Hstring.t * 'a S.t) list; read_st : 'a S.t; write_st : 'a S.t}
	
    let init () = {syst = []; init = []; read_st = S.init (); write_st = S.init ()}

    let get_v s h = let state = s.read_st in
		    S.get_v state h
    let get_a s h = let state = s.read_st in
  		    S.get_a state h
    let get_e s h pl = let state = s.read_st in
  		       S.get_e state h pl

    let set_v s h v = let state = s.write_st in
  		      S.set_v state h v
    let set_a s h a = let state = s.write_st in
  		      S.set_a state h a
    let set_e s h pl v = let state = s.write_st in
  			 S.set_e state h pl v

    let exists f s = List.exists (fun (_, e) -> f e) s

    let update_init s il = {s with init = il::s.init}

    let get_init s = s.init

    let new_init tr s i = {syst = (tr, S.copy i) :: s.syst; init = s.init; read_st = S.copy i; write_st = i}

    let update_s tr s = {syst = (tr, S.copy s.write_st) :: s.syst; init = []; read_st = S.copy s.write_st; write_st = s.write_st}

  end
				  

(* GLOBAL VARIABLES *)

module Etat = State (DimArray)
module Syst = System (Etat)

let system = ref (Syst.init ())

(* Types *)
let htbl_types = Hashtbl.create 11

let htbl_abstypes = Hashtbl.create 11

(* Filling htbl_types with default types (proc, bool, int and real) *)
let () = 
  List.iter (
    fun (constr, fields) -> 
      Hashtbl.add htbl_types constr fields
  ) [ Hstring.make "proc", List.map (fun i -> Proc i) list_threads;
      Hstring.make "bool", [Hstr Ast.hfalse; Hstr Ast.htrue];
      Hstring.make "int", [Numb (Int 0)];
      Hstring.make "real", [Numb (Int 0)]
    ]

let compare_value v1 v2 = 
  match v1, v2 with
    | Numb n1, Numb n2 -> Num.compare_num n1 n2
    | Hstr h1, Hstr h2 
    | Var h1, Var h2 -> Hstring.compare h1 h2
    | Proc p1, Proc p2 -> Pervasives.compare p1 p2
    | _ -> assert false

module TS = Set.Make (struct type t = value let compare = compare_value end)
module TI = Set.Make (struct type t = Hstring.t let compare = Hstring.compare end)

(* This hashtbl contains variables binded to their representant
   and their type *)
let ec = Hashtbl.create 17
(* This hashtbl contains variables binded to :
   - int or real : the list of their forbiddent values
   - rest : the list of their possible values
   and the list of the representants with which they differ *)
let dc = Hashtbl.create 17

let inits = ref []

(* If their is only one possible value left,
   delete the variables from the difference classes
   and update the equivalence classes with this value *)
let upd_dc h types ty diffs =
  if TS.cardinal types == 1 && ty <> N && ty <> A
  then
    (
      Hashtbl.remove dc h;
      let v = TS.choose types in
      Hashtbl.iter (
	fun n' (rep, tself) ->
	  match rep with
	    | Var h' -> if (h' = h)
	      then Hashtbl.replace ec n' (v, tself)
	    | _ -> ()
      ) ec;
      Hashtbl.iter (
	fun n' (ty, types, diffs) ->
	  if (TI.mem h diffs)
	  then let diffs' = TI.remove h diffs in
	       let types' = TS.remove v types in
	       Hashtbl.replace dc n' (ty, types', diffs')
      ) dc
    )
  else Hashtbl.replace dc h (ty, types, diffs)

(* Containing the groups of bounded variables *)
let groups = Hashtbl.create 17

(* Containing the sorted groups of bounded variables *)
let graphs = Hashtbl.create 17



(* USEFUL METHODS *)


(* Tranform a constant in a num *)
let value_c c =
  match MConst.is_num c with
    | Some e -> e
    | None -> error (MustBeSingleNum)

(* Return the operator on int (for proc) *)
let find_op =
  function
    | Eq -> (=)
    | Lt -> (<)
    | Le -> (<=)
    | Neq -> (<>)

(* Return the operator on Num.num (for int and real) *)
let find_nop =
  function
    | Eq -> (=/)
    | Lt -> (</)
    | Le -> (<=/)
    | Neq -> (<>/)

(* Return the first type constructor *)
let default_type g_type =
  if Hashtbl.mem htbl_abstypes g_type 
  then raise Exit 
  else
    match Hashtbl.find htbl_types g_type with
      | hd::_ -> hd
      | _ -> assert false

(* Intersection of two int lists *)
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

(* Return the name of the representant (Hstring.t) *)
let rep_name n =
  let (rep, _) = Hashtbl.find ec n in
  match rep with
    | Var id -> id
    | _ -> raise ConstrRep

let hst_var =
  function
    | Var h -> h
    | _ -> assert false

let ec_replace n v =
  Hashtbl.iter (
    fun n' (rep, st) ->
      if rep = n
      then Hashtbl.replace ec n' (v, st)
  ) ec

(* VALUE METHODS *)

(* Return a constant value *)
let get_cvalue =
  function
    | Const c -> Numb (value_c c)
    | Elem (id, Constr) -> Hstr id
    | _ -> assert false

(* Return a constant value or the value of a variable
   (global or array) *)
let get_value sub =
  function
    | (Const _ as v) | (Elem (_, Constr) as v) -> get_cvalue v
    | Elem (id, Glob) -> Syst.get_v !system id
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
      Syst.get_e !system id ind
    | _ -> assert false

let v_equal v1 v2 =
  match v1, v2 with
    | Var h1, Var h2
    | Hstr h1, Hstr h2 -> Hstring.equal h1 h2
    | Numb i1, Numb i2 -> i1 =/ i2
    | Proc p1, Proc p2 -> p1 = p2
    | _ -> false


(* DISPLAY METHODS *)

let print_value f v =
  match v with
    | Numb i -> printf "%s " (Num.string_of_num i)
    | Proc p -> printf "%d " p
    | Hstr h -> printf "%a " Hstring.print h
    | Var h -> printf "%a " Hstring.print h

let print_ce_diffs () =
  printf "\nce :@.";
  Hashtbl.iter (
    fun n (rep, tself) ->
      printf "%a : %a@." Hstring.print n print_value rep
  ) ec;
  printf "\nDc@.";
  Hashtbl.iter (
    fun n (ty, types, diffs) ->
      printf "%a : " Hstring.print n;
      TS.iter (printf "%a " print_value) types;
      TI.iter (printf "%a " Hstring.print) diffs;
      printf "@."
  ) dc;
  printf "@."

let print_g () =
  Hashtbl.iter (
    fun c l ->
      printf "%d :@." c;
      List.iter (
	fun (n, (ty, types, diffs)) ->
	  printf "%a : " Hstring.print n;
	  TS.iter (printf "%a " print_value) types;
	  TI.iter (printf "%a " Hstring.print) diffs;
	  printf "@."
      ) l;
  ) graphs;
  printf "@."

let print_groups () =
  Hashtbl.iter
    (fun i ti ->
      printf "%d :@." i;
      TI.iter (
	fun n -> printf " %a" Hstring.print n
      ) ti;
      printf "@."
    ) groups

let print_inits () =
  List.iter (
    fun (n, (tself, ts)) ->
      printf "%a (" Hstring.print n;
      (match tself with
	| RGlob h -> printf "G %a) : " Hstring.print h
	| RArr (h, i) -> printf "A %a %d) : " Hstring.print h i
      );
      TS.iter (
	fun v -> printf "%a " print_value v
      ) ts;
      printf "@."
  ) !inits

let print_system (tr, {Etat.globs; Etat.arrs}) =
  printf "@.";
  printf "%a@." Hstring.print tr;
  Hashtbl.iter (
    fun var value ->
      printf "%a -> %a@." Hstring.print var print_value value
  ) globs;
  Hashtbl.iter (
    fun name tbl -> printf "%a " Hstring.print name;
      DimArray.print tbl print_value;
      printf "@."
  ) arrs;
  printf "@."

let print_init () =
  List.iter print_system (Syst.get_init !system)



(* INITIALIZATION METHODS *)


(* Each type is associated to his constructors 
   The first one is considered as the default type *)
let init_types type_defs globals arrays =
  List.iter (
    fun (t_name, t_fields) ->
      if not (Hashtbl.mem htbl_types t_name) then
	let fields = 
	  if (List.length t_fields > 0)
	  then 
	    List.fold_right (
	      fun field acc -> (Hstr field)::acc
	    ) t_fields [] 
	  else
	    (
	      Hashtbl.add htbl_abstypes t_name ();
	      let acc' =
		List.fold_left (
		  fun acc (n, ty) -> if ty = t_name then (Hstr n)::acc else acc) [] globals in
	      List.fold_left (
		fun acc (n, (_, ty)) -> if ty = t_name then (Hstr n)::acc else acc) acc' arrays
	    )
	in
	Hashtbl.add htbl_types t_name fields
  ) type_defs
    
(* Initialization of the global variables to their
   default constructor, of the equivalence classes and
   of the difference classes *)
let init_globals globals =
  let i = Hstring.make "int" in
  let r = Hstring.make "real" in
  List.iter (
    fun (g_name, g_type) ->
      (* First, each var is its own representant *)
      Hashtbl.add ec g_name (Var g_name, RGlob g_type);
      let ty, stypes, diffs = 
	if (Hstring.equal g_type i || Hstring.equal g_type r) 
	(* Int or real*)
	then N, TS.empty, TI.empty
	(* Abstract or other type*)
	else
	  let ty = Hashtbl.find htbl_types g_type in
	  if Hashtbl.mem htbl_abstypes g_type 
	  then
	    let ti = List.fold_left (
	      fun acc t -> match t with
		| Var h when h != g_name -> TI.add h acc
		| _ -> acc
	    ) TI.empty ty in
	    A, TS.singleton (Var g_name), ti 
	  else 
	    let st = List.fold_left (fun acc t -> TS.add t acc) TS.empty ty in
	    O, st, TI.empty 
      in
      Hashtbl.add dc g_name (ty, stypes, diffs)
  ) globals

(* Initialization of the arrays with their default
   constructor (deterministic version) of the equivalence classes and
   of the difference classes *)
let init_arrays arrays =
  let i = Hstring.make "int" in
  let r = Hstring.make "real" in
  List.iter (
    fun (a_name, (a_dims, a_type)) ->
      let dims = List.length a_dims in
      Hashtbl.add ec a_name (Var a_name, RArr (a_type, dims));
      let ty, stypes, diffs = 
	if (Hstring.equal a_type i || Hstring.equal a_type r) 
	(* Int or real *)
	then N, TS.empty, TI.empty
	(* Other type *)
	else
	  let ty = Hashtbl.find htbl_types a_type in
	  if Hashtbl.mem htbl_abstypes a_type 
	  then
	    let ti = List.fold_left (
	      fun acc t -> match t with
		| Var h when h != a_name -> TI.add h acc
		| _ -> acc
	    ) TI.empty ty in
	    A, TS.singleton (Var a_name), ti
	  else 
	    let st = List.fold_left (fun acc t -> TS.add t acc) TS.empty ty in
	    O, st, TI.empty
      in
      Hashtbl.add dc a_name (ty, stypes, diffs)
  ) arrays
    
(* Execution of the real init method from the cubicle file 
   to initialize the equivalence classes and difference classes *)
let init_htbls (vars, atoms) =
  List.iter (
    fun satom ->
      SAtom.iter (
	fun atom ->
	  match atom with
	    | Comp (t1, Eq, t2) ->
	      begin
		match t1, t2 with
		  (* Var = Const or Const = Var *)
		  | (Elem (id1, Glob) | Access (id1, _)), ((Elem (_, Constr) | Const _) as r) 
		  | ((Elem (_, Constr) | Const _) as r), (Elem (id1, Glob) | Access (id1, _)) ->
	    	    let (rep, _) = Hashtbl.find ec id1 in
		    let h = hst_var rep in
		    let v = get_cvalue r in
		    (* Change the representant of the equivalence class with the constant. 
		       Remove the equivalence class from the difference classes hashtbl *)
		    Hashtbl.iter (
		      fun n' (rep', st) ->
			if rep' = rep
			then
			  (
			    Hashtbl.remove dc n';
			    Hashtbl.replace ec n' (v, st)
			  )
		    ) ec;
		    (* Change the difference classes so the representant 
		       is now an impossible value *)
		    Hashtbl.iter (
		      fun n (ty, types, diffs) ->
			if (TI.mem h diffs)
			then let diffs' = TI.remove h diffs in
			     let types' = 
			       match ty with
				 | N -> TS.add v types
				 | O | A -> TS.remove v types 
			     in
			     upd_dc n types' ty diffs';
		    ) dc
		      
		  (* Var or Tab[] = Var or Tab[] *)
		  | (Elem (id1, Glob) | Access (id1, _)), (Elem (id2, Glob) | Access (id2, _)) ->
		    let (rep, _) as t1 = Hashtbl.find ec id1 in
		    let t2 = Hashtbl.find ec id2 in
		    let ids, idd, (sr, _), (dr, dts) = 
		      match rep with
			| Var _ -> id2, id1, t2, t1
			| _ -> id1, id2, t1, t2 
		    in
		    (match sr with
		      (* If the future representant is not a constant,
			 modify the difference class of the representant. *)
		      | Var _ -> let (ty1, types1, diffs1) = Hashtbl.find dc ids in
				 let (ty2, types2, diffs2) = Hashtbl.find dc idd in
				 let types = 
				   match ty1 with
				     | A -> types1
				     | N -> TS.union types1 types2
				     | O -> TS.inter types1 types2
				 in 
				 let diffs = TI.union diffs1 diffs2 in 
				 upd_dc ids types ty1 diffs;
		      | _ -> ()
		    );
		    (* Remove the non-chosen variable from the difference classes hashtbl *)
		    Hashtbl.remove dc idd;
		    (* Modify the representant of each variable which representant was the 
		       non-chosen variable *)
		    ec_replace dr sr	    		 
		  | _ -> assert false
	      end
	    | Comp (t1, Neq, t2) ->
	      begin
	    	match t1, t2 with
		  (* Var or Tab[] <> Const or Const <> Var or Tab[] *)
	    	  | (Elem (id1, Glob) | Access (id1, _)), ((Elem (_, Constr) | Const _) as c) 
		  | ((Elem (_, Constr) | Const _) as c), (Elem (id1, Glob) | Access (id1, _)) ->
		    (* Delete the constr from the possible values of the variable representant *)
		    begin
		      try
			let h = rep_name id1 in
	    		let (ty, types, diffs) = Hashtbl.find dc h in
	    		let v = get_cvalue c in
			let types' = match ty with
			  | N -> TS.add v types
			  | O | A -> TS.remove v types 
			in
			upd_dc h types' ty diffs
		      with ConstrRep -> () (* Strange but allowed *)
		    end
		  (* Var or Tab[] <> Var or Tab[] *)
	    	  | (Elem (id1, Glob) | Access (id1, _)), (Elem (id2, Glob) | Access (id2, _)) ->
	    	    begin
		      let (rep1, tself1) = Hashtbl.find ec id1 in
		      let (rep2, tself2) = Hashtbl.find ec id2 in
		      match rep1, rep2 with
			| Var h1, Var h2 -> let (ty1, types1, diffs1) = Hashtbl.find dc h1 in
	    				    let (ty2, types2, diffs2) = Hashtbl.find dc h2 in
	    				    Hashtbl.replace dc h1 (ty1, types1, TI.add h2 diffs1);
	    				    Hashtbl.replace dc h2 (ty2, types2, TI.add h1 diffs2)
	    		| Var h, (_ as rep') 
			| (_ as rep'), Var h -> 	
			  let (ty, types, diffs) = Hashtbl.find dc h in
			  let types' = match ty with
			    | N -> TS.add rep' types
			    | O | A -> TS.remove rep' types
			  in upd_dc h types' ty diffs
			  
			| _ -> () (* Strange but that's your problem *)
		    end
		  | Elem (id, Glob), Elem (p, Var)
		  | Elem (p, Var), Elem (id, Glob) ->
		    let h = rep_name id in
		    let (ty, _, diffs) = Hashtbl.find dc h in
		    Hashtbl.replace dc h (ty, TS.singleton !fproc, diffs)
		  | _ -> assert false
	      end
	    | _ -> assert false
      ) satom
  ) atoms

let c = ref 0

let update () =
  let dc' = Hashtbl.copy dc in
  let rec upd_diff diff =
    TI.iter (
      fun n' -> 
	let ti = Hashtbl.find groups !c in
	(if not (TI.mem n' ti)
	 then
	    ( 
	      let (_, _, diffs') = Hashtbl.find dc' n' in
	      Hashtbl.replace groups !c (TI.add n' ti);
	      Hashtbl.remove dc' n';
	      upd_diff diffs'
	    )
	)
    ) diff in
  Hashtbl.iter (
    fun n (_, types, diffs) ->
      Hashtbl.add groups !c (TI.singleton n);
      Hashtbl.remove dc' n;
      upd_diff diffs;
      incr c
  ) dc'

let comp_node (h1, (_, ty1, di1)) (h2, (_, ty2, di2)) =
  let ct1 = TS.cardinal ty1 in
  let ct2 = TS.cardinal ty2 in
  if ct1 < ct2
  then -1
  else 
    (
      if ct1 > ct2
      then 1
      else (
	let cd1 = TI.cardinal di1 in
	let cd2 = TI.cardinal di2 in
	if cd1 > cd2
	then -1
	else 
	  if cd1 < cd2 then 1
	  else 0
      )
    )

let upd_graphs () =
  Hashtbl.iter (
    fun i ti ->
      let list =
	TI.fold (
	  fun e l -> 
	    let elt = Hashtbl.find dc e in
	    (e, elt)::l
	) ti [] in
      let slist = List.sort comp_node list in
      Hashtbl.add graphs i slist;
      incr c  
  ) groups  

let graphs_to_inits () =
  let rec l_to_ec v niv ti rtl =
    match rtl with
      | ((n, (_, ts, ti')) as hd)::tl ->
	if (not (TI.mem n ti)) && (TS.mem v ts)
	then
	  (
	    let (_, tself) = Hashtbl.find ec n in
	    inits := (n ,(tself, (TS.singleton v))) :: !inits;
	    l_to_ec v niv (TI.union ti ti') tl
	  )
	else l_to_ec v (hd::niv) ti tl
      | _ -> niv
  in
  let rec new_v_l n ats fts ti tl =
    let v = TS.min_elt ats in
    let (_, tself) = Hashtbl.find ec n in
    inits := (n ,(tself, (TS.singleton v))) :: !inits;
    let niv = (List.rev (l_to_ec v [] ti tl)) in
    match niv with
      | (n, (_, ts, ti))::tl -> let ats = TS.remove v (TS.diff ts fts) in
				let fts = TS.add v fts in
				new_v_l n ats fts ti tl
      | _ -> ()
  in
  Hashtbl.iter (
    fun i lv ->
      match lv with
	| [(n, (_, ts, ti))] -> let v = TS.choose ts in
				let vs = match v with
				  | Hstr _ -> ts
				  | Proc p -> if init_proc then TS.union (TS.singleton v) (TS.singleton !fproc)
				    else TS.singleton v
				  | _ -> TS.singleton v
				in 
				let (_, tself) = Hashtbl.find ec n in
				inits :=  (n ,(tself, vs)) :: !inits
	| (n, (_, ts, ti))::tl -> new_v_l n ts TS.empty ti tl
	| _ -> assert false
  ) graphs

let ec_to_inits () =
  Hashtbl.iter (
    fun n (rep, tself) ->
      try
	let vs =
	  match rep with
	    | Var h -> if h = n then raise Exit else let (_, vs) = List.assoc h !inits in vs
	    | _ -> TS.singleton rep
	in inits :=  (n, (tself, vs)) :: !inits
      with Exit -> ()
  ) ec;
  let comparei (_, (_, ts1)) (_, (_, ts2)) =
    let lts1 = TS.cardinal ts1 in
    let lts2 = TS.cardinal ts2 in
    Pervasives.compare lts1 lts2
  in
  inits := List.sort comparei !inits
    
let initialization init =
  init_htbls init; 
  update ();
  (* print_groups (); *)
  upd_graphs ();
  (* print_ce_diffs (); *)
  (* print_g (); *)
  graphs_to_inits ();
  ec_to_inits ();
  (* print_inits (); *)
  (* print_ce_diffs (); *)
  let etati = Etat.init () in
  let c = ref 0 in
  let upd_etati tself n v =
    let value_list al =
      List.map (
	fun (id, n) ->
	  (Hstr id, n)
      ) al
    in
    match tself with
      | RGlob _ -> Etat.set_v etati n v
      | RArr (_, d) -> let tbl =
			 try let al = Hashtbl.find tab_init n in
			     let vl = value_list al in
			     DimArray.minit d nb_threads vl v
			 with Not_found -> DimArray.init d nb_threads v
		       in
		       Etat.set_a etati n tbl
  in     
  let rec create_init l =
    match l with
      | [(n, (tself, ts))] -> 
	TS.iter (fun v -> 
	  upd_etati tself n v;
	  incr c;
	  let i = Etat.copy etati in
	  let tr = Hstring.make ("init" ^ (string_of_int !c)) in
	  system := Syst.update_init !system (tr, i)
	) ts
      | (n, (tself, ts)) :: tl -> 
	TS.iter (
	  fun v -> 
	    upd_etati tself n v;
	    create_init tl
	) ts
      | _ -> assert false
  in 
  create_init !inits;
  printf "%d@." (List.length (Syst.get_init !system))


(* SUBSTITUTION METHODS *)

       
(* Here, optimization needed if constant values *)     
let subst_req sub req =
  let f = fun () ->
    match req with
      | True -> raise ETrue
      | False -> raise EFalse
      | Comp (t1, op, t2) -> 
	let t1_v = get_value sub t1 in
	let t2_v = get_value sub t2 in
	begin 
	  match t1_v, t2_v with
	    | Numb n1, Numb n2 ->
	      let op' = find_nop op in
	      op' n1 n2
	    | Proc p1, Proc p2 -> 
	      let op' = find_op op in
	      op' p1 p2
	    | Hstr h1, Hstr h2 ->
	      begin
		match op with
		  | Eq -> Hstring.equal h1 h2
		  | Neq -> not (Hstring.equal h1 h2)
		  | _ -> assert false
	      end
	    (* Problem with ref_count.cub, assertion failure *)
	    | Hstr h, Proc i1 -> let (p, _) = List.find (fun (_, i) -> i1 = i) sub in 
				 printf "TODO %a, %a = %d@." Hstring.print h Hstring.print p i1; 
				 exit 1
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
		 Syst.set_v !system var value)::acc
  ) [] assigns in
  let subst_upds = List.fold_left (
    fun tab_acc u -> 
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
		  let f = fun () ->
		    let t = get_value s term in
		    let arr = Syst.get_a !system u.up_arr in
		    DimArray.set arr pl t;
		    Syst.set_a !system u.up_arr arr
		  in
		  (filter, f)::disj_acc
	      ) u.up_swts []
	    in supd::upd_acc
	) [] subs
      in upd_tab::tab_acc
  ) [] upds in
  (subst_assigns, subst_upds)
    

(* SYSTEM INIT *)

let init_system se =
  init_types se.type_defs se.globals se.arrays;
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
  (name, updts)



(* SYSTEM UPDATE *)


let update_system () =
  let (tr, (assigns, updates)) = random_transition () in
  List.iter (fun a -> a ()) assigns;
  let updts = valid_upd updates in 
  List.iter (fun us -> List.iter (fun u -> u ()) us ) updts;
  system := Syst.update_s tr !system
    
(* INTERFACE WITH BRAB *)

let get_value_st sub st =
  function
    | Const c -> Numb (value_c c)
    | Elem (id, Glob) -> Etat.get_v st id
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
      Etat.get_e st id ind
    | _ -> assert false

let contains sub sa s =
  Syst.exists (
    fun state ->
      SAtom.for_all (
	fun a ->
	  match a with
	    | True -> true
	    | False -> false
	    | Comp (t1, op, t2) -> 
	      let t1_v = get_value_st sub state t1 in
	      let t2_v = get_value_st sub state t2 in
	      begin
		match t1_v, t2_v with
		  | Numb n1, Numb n2 ->
		    let op' = find_nop op in
		    op' n1 n2
		  | Proc p1, Proc p2 -> 
		    let op' = find_op op in
		    op' p1 p2
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
      ) sa
  ) !system.Syst.syst
    
let filter t_syst_l =
  try
    let rcube = List.find (
      fun t_syst -> let (pl, sa) = t_syst.t_unsafe in
		    let subst = Ast.all_permutations pl list_threads in
		    List.for_all (
		      fun sub ->
			not (contains sub sa !system)
		    ) subst
    ) t_syst_l in
    Some rcube
  with Not_found -> None

(* MAIN *)

    
let scheduler se =
  Random.self_init ();
  init_system se;
  init_transitions se.trans;
  let total = ref 1 in
  List.iter (
    fun (tr, st) ->
      system := Syst.new_init tr !system st;
      let count = ref 1 in
      (
	try
	  while !count < nb_exec do
	    update_system ();
	    incr count;
	    incr total
	  done;
	with Invalid_argument _ -> ()
      );
  ) (Syst.get_init !system);
  if verbose > 0 then
    begin
      let count = ref 1 in
      List.iter (
	fun st -> printf "%d : " !count; incr count; print_system st
      ) (List.rev !system.Syst.syst)
    end;
  printf "Scheduled %d states\n" !total;
  printf "--------------------------@."    
    
let dummy_system = {
  globals = [];
  consts = [];
  arrays = [];
  type_defs = [];
  init = [],[];
  invs = [];
  cands = [];
  unsafe = [];
  forward = [];
  trans = [];
}


let current_system = ref dummy_system

let register_system s = current_system := s

let run () =
  assert (!current_system <> dummy_system);
  scheduler !current_system
