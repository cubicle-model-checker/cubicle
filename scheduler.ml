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
exception ConstrRep

exception TEnd of int
exception Error of error


let () =
  let report (b,e) file =
    let l = b.pos_lnum in
    let fc = b.pos_cnum - b.pos_bol + 1 in
    let lc = e.pos_cnum - b.pos_bol + 1 in
    printf "File \"%s\", line %d, characters %d-%d:" file l fc lc
  in
  try
    let file = (Filename.chop_extension file)^".sched" in
    let cin = try open_in file
      with Sys_error _ -> raise Exit
    in
    let lb = Lexing.from_channel cin in
    try 
      Parser.scheduler Lexer.token lb
    with 
	Parsing.Parse_error ->
	  let  loc = (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb) in
	  report loc file;
          printf "\nsyntax error\n@.";
	  exit 2
  with Exit -> ()
    
let init_proc = !init_proc

let error e = raise (Error e)

let compare_value v1 v2 =
  match v1, v2 with
    | Numb n1, Numb n2 -> Num.compare_num n1 n2
    | Numb _, _ -> -1
    | _, Numb _ -> -1
    | Hstr h1, Hstr h2 -> Hstring.compare h1 h2
    | Hstr _, _ -> -1
    | _, Hstr _ -> 1
    | VVar h1, VVar h2 -> Pervasives.compare h1 h2
    | VVar _, _ -> -1
    | _, VVar _ -> 1
    | Proc p1, Proc p2 -> Pervasives.compare p1 p2

let vequal v1 v2 =
  if compare_value v1 v2 = 0 then true else false

let print_value f v =
  match v with
    | Numb i -> printf "%s " (Num.string_of_num i)
    | Proc p -> printf "%d " p
    | Hstr h -> printf "%a " Hstring.print h
    | VVar h -> printf "%a " Hstring.print h

type stype =
  | RGlob of Hstring.t
  | RArr of (Hstring.t * int)

let hst = function 			
  | RGlob h | RArr (h, _) -> h 

type ty =
  | A (* abstract type *)
  | N (* int or real *)
  | O (* everything else *)

(* List of processes *)
let list_threads = 
  let rec lthreads l =
    function
      | n when n = nb_threads ->  l
      | n -> n::(lthreads l (n+1))
  in lthreads [] 0

(* This list will contain all the transitions *)
let trans_list = ref []

module type OrderedType =
  sig 
    type t
    val compare : t -> t -> int
  end

module OrderedValue =
  struct
    type t = value
    let compare = compare_value
  end

(* Module to manage multi-dimensional arrays *)
module type DA = sig
    
  type elt

  type t

  val init : int -> int -> elt -> t
  val minit : int -> int -> (elt * int) list -> elt -> t
  val get : t -> int list -> elt
  val set : t -> int list -> elt -> unit
  val print : t -> (Format.formatter -> elt -> unit) -> unit
  val copy : t -> t
  val dim : t -> int
  val dcompare : t -> t -> int
  val equal : t -> t -> bool
    
end 

module DimArray (Elt : OrderedType) : DA with type elt = Elt.t = struct
    
  type elt = Elt.t
    
  type dima = 
    | Arr of Elt.t array 
    | Mat of dima array

  type t = {dim:int; darr:dima}

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
		     for j = !i to !i + n - 1 do
		       a.(j) <- c
		     done;
		     i := !i + n
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

  let dcompare t1 t2 =
    let c = ref 0 in
    let rec compare' t1 t2 =
      match t1, t2 with
	| Arr a1, Arr a2 ->
	  (try
	     Array.iteri (
	       fun i e -> 
		 c := Elt.compare a2.(i) e;
		 if !c <> 0 then raise Exit
	     ) a1;
	     !c
	   with Exit -> !c
	  )
	| Mat m1, Mat m2 ->
	  (try
	     Array.iteri (
	       fun i a -> 
		 c := compare' a m2.(i);
		 if !c <> 0 then raise Exit
	     ) m1;
	     !c
	   with Exit -> !c
	  )
	| _ -> assert false
    in compare' t1.darr t2.darr

  let equal t1 t2 =
    if dcompare t1 t2 = 0 then true else false

end

module type St = sig

  type elt
  type da

  (* The state : global variables and arrays *)
  type t = {globs :(Hstring.t, elt) Hashtbl.t; arrs : (Hstring.t, da) Hashtbl.t}
      
  val init : unit -> t

  val giter : (Hstring.t -> elt -> unit) -> (Hstring.t, elt) Hashtbl.t -> unit
  val aiter : (Hstring.t -> da -> unit) -> (Hstring.t, da) Hashtbl.t -> unit
    
  val ecompare : t -> t -> int
  val equal : t -> t -> bool
    
  (* Get a global variable value *)
  val get_v : t -> Hstring.t -> elt
  (* Get an array by its name *)
  val get_a : t -> Hstring.t -> da
  (* Get an element in an array by its name and a a param list*)
  val get_e : t -> Hstring.t -> int list -> elt
    
  (* Set a global variable value *)
  val set_v : t -> Hstring.t -> elt -> unit
  (* Set an array by its name and a new array *)
  val set_a : t -> Hstring.t -> da -> unit
  (* Set an element in an array by its name, a param list and a value *)
  val set_e : t -> Hstring.t -> int list -> elt -> unit
    
  val copy : t -> t
    
end

module State (Elt : OrderedType)  (A : DA with type elt = Elt.t) : St with type elt = Elt.t and type da = A.t = struct

  type elt = Elt.t 
  type da = A.t
  type t = {globs: (Hstring.t, elt) Hashtbl.t; arrs: (Hstring.t, da) Hashtbl.t}

  let init () = {globs = Hashtbl.create 17; arrs = Hashtbl.create 17}

  let giter = Hashtbl.iter
  let aiter = Hashtbl.iter

  let ecompare s1 s2 =
    let c = ref 0 in
    try
      let gs1 = s1.globs in
      let gs2 = s2.globs in
      Hashtbl.iter (
  	fun g v1 -> let v2 = Hashtbl.find gs2 g in
  		    c := Elt.compare v1 v2;
  		    if !c <> 0 then raise Exit
      ) gs1;
      let as1 = s1.arrs in
      let as2 = s2.arrs in
      Hashtbl.iter (
  	fun a arr1 -> let arr2 = Hashtbl.find as2 a in
  		      c := (A.dcompare arr1 arr2);
  		      if !c <> 0 then raise Exit
      ) as1;
      !c
    with Exit -> !c

  let iter_globs = Hashtbl.iter

  let equal s1 s2 = if ecompare s1 s2 = 0 then true else false

  let get_v t h = try Hashtbl.find t.globs h with Not_found -> eprintf "%a@." Hstring.print h; exit 1
  let get_a t h = try Hashtbl.find t.arrs h with Not_found -> eprintf "%a@." Hstring.print h; exit 1
  let get_e t h pl = let arr = get_a t h in
  		     try A.get arr pl
		     with Not_found -> eprintf "%a@." Hstring.print h; exit 1

  let set_v t h v = Hashtbl.replace t.globs h v
  let set_a t h arr = Hashtbl.replace t.arrs h arr
  let set_e t h pl v = let arr = get_a t h in
  		       A.set arr pl v

  let copy t = let carrs = Hashtbl.copy t.arrs in
  	       Hashtbl.iter (fun name arr -> Hashtbl.replace carrs name (A.copy arr)) carrs;
  	       {globs = Hashtbl.copy t.globs; arrs = carrs}

end	

	  
(* GLOBAL VARIABLES *)

module Array = DimArray (OrderedValue)
module Etat = State (OrderedValue) (Array)
module Syst = Map.Make (
  struct
    type t = Etat.t
    let compare = Etat.ecompare
  end
)
	
open Syst

let system = ref (Syst.empty)
let sinits = ref (Syst.empty)

let read_st = ref (Etat.init ())
let write_st = ref (Etat.init ())

(* Types *)
let htbl_types = Hashtbl.create 11

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

module TI = Set.Make (
  struct 
    type t = Hstring.t 
    let compare = Hstring.compare 
  end
)

module TS = Set.Make (
  struct 
    type t = value 
    let compare = compare_value 
  end
)

module TIS = Set.Make (
  struct 
    type t = Hstring.t * TS.t * TI.t
    let compare (v1, ts1, ti1) (v2, ts2, ti2) = 
      let ct1 = TS.cardinal ts1 in
      let ct2 = TS.cardinal ts2 in
      if ct1 > ct2
      then -1
      else 
	(
	  if ct1 < ct2
	  then 1
	  else (
	    let cd1 = TI.cardinal ti1 in
	    let cd2 = TI.cardinal ti2 in
	    if cd1 < cd2
	    then -1
	    else 
	      if cd1 > cd2 then 1
	      else Hstring.compare v1 v2
	  )
	)
  end
)

let htbl_abstypes = Hashtbl.create 11

(* This hashtbl contains variables binded to their representant
   and their type *)
let ec = Hashtbl.create 17
(* This hashtbl contains variables binded to :
   - int or real : the list of their forbiddent values
   - rest : the list of their possible values
   and the list of the representants with which they differ *)
let dc = Hashtbl.create 17

let inits = Hashtbl.create 17

let init_list = ref []

let ntValues = Hashtbl.create 17

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
    | VVar id -> id
    | _ -> raise ConstrRep

let hst_var =
  function
    | VVar h -> h
    | _ -> assert false

let ec_replace rep v =
  Hashtbl.iter (
    fun n' (rep', st) ->
      if rep' = rep
      then Hashtbl.replace ec n' (v, st)
  ) ec

let abst_replace id rep ts =
  Hashtbl.iter (
    fun a' (rep', ts') ->
      if rep' = id
      then Hashtbl.replace htbl_abstypes a' (rep, (TI.union ts ts'))
  ) htbl_abstypes

(* VALUE METHODS *)

(* Return a constant value *)
let get_cvalue =
  function
    | Const c -> Numb (value_c c)
    | Elem (id, Constr) -> Hstr id
    | _ -> assert false

(* Return a constant value or the value of a variable
   (global or array) *)
let rec get_value sub =
  function
    | (Const _ as v) | (Elem (_, Constr) as v) -> get_cvalue v
    | Elem (id, Glob) -> (try Etat.get_v !read_st id with Not_found -> eprintf "%a@." Hstring.print id; exit 1)
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
      Etat.get_e !read_st id ind
    | Arith (t,  c) -> 
      let v = get_value sub t in
      let v' = value_c c in
      match v with
	| Numb n -> Numb ((+/) n v')
	| _ -> assert false
	  
let v_equal v1 v2 =
  match v1, v2 with
    | VVar h1, VVar h2
    | Hstr h1, Hstr h2 -> Hstring.equal h1 h2
    | Numb i1, Numb i2 -> i1 =/ i2
    | Proc p1, Proc p2 -> p1 = p2
    | _ -> false

let type_st st = match st with RGlob t | RArr (t, _) -> t

(* DISPLAY METHODS *)

let print_value f v =
  match v with
    | Numb i -> printf "%s " (Num.string_of_num i)
    | Proc p -> printf "%d " p
    | Hstr h -> printf "%a " Hstring.print h
    | VVar h -> printf "%a " Hstring.print h

let print_ce () =
  printf "\nce :@.";
  Hashtbl.iter (
    fun n (rep, tself) ->
      printf "%a : %a %a@." Hstring.print n print_value rep Hstring.print (hst tself)
  ) ec

let print_diffs () = 
  printf "\nDc@.";
  Hashtbl.iter (
    fun n (ty, types, diffs, cfc) ->
      printf "%a : " Hstring.print n;
      printf "\n\tTS : ";
      TS.iter (printf "%a " print_value) types;
      printf "\n\tTI : ";
      TI.iter (printf "%a " Hstring.print) diffs;
      printf "\n\tcfc : %d@." cfc
  ) dc;
  printf "@."

let print_ntv () = 			
  printf "\nntV@."; 			
  Hashtbl.iter ( 			
    fun n vl -> 			
      printf "%a : " Hstring.print n; 			
      List.iter (printf "%a " print_value) vl; 			
      printf "@." 			
  ) ntValues 

let print_abst () =
  printf "\nAbst :@.";
  Hashtbl.iter (
    fun n (rep, ts) -> 
      printf "%a -> %a, diffs " Hstring.print n Hstring.print rep;
      TI.iter (printf "%a " Hstring.print) ts;
      printf "@."
  ) htbl_abstypes

let print_types () =
  printf "\nTypes :@.";
  Hashtbl.iter (
    fun n vl ->
      printf "t : %a -> " Hstring.print n;
      List.iter (printf "%a " print_value) vl; 
      printf "@."
  ) htbl_types

let print_inits () =
  printf "\n INITS \n\n";
  Hashtbl.iter (
    fun cfc tis ->
      printf "%d :\n\t" cfc; 
      TIS.iter
	(fun (rep', ts', ti') ->
	  printf "%a -> " Hstring.print rep';
	  TS.iter (printf "%a " print_value) ts';
	  printf "| ";
	  TI.iter (printf "%a " Hstring.print) ti';
	  printf "\n\t";
	) tis;
      printf "\n"
  ) inits;
  printf "@."

let print_init_list () =
  List.iter
    (fun (rep, st, ts, ce) ->
      printf "%a -> " Hstring.print rep;
      TS.iter (printf "%a " print_value) ts;
      printf "\n";
      List.iter (fun (n, _) -> printf "%a " Hstring.print n) ce;
      printf "@.";
    ) !init_list

let print_state {Etat.globs; Etat.arrs} =
  Etat.giter (
    fun var value ->
      printf "\t%a -> %a@." Hstring.print var print_value value
  ) globs;
  Etat.aiter (
    fun name tbl -> printf "\t%a " Hstring.print name;
      Array.print tbl print_value;
      printf "@."
  ) arrs

let print_system st trl =
  printf "@.";
  let lrt = List.rev trl in
  List.iter (
    fun (t, args) -> 
      printf "%a(%a)@." Hstring.print t 
	(Hstring.print_list " ") (List.rev args)
  ) lrt;
  print_state st;
  printf "@."

let print_init () =
  Syst.iter print_system (!sinits)

let print_procinit () =
  printf "Proc_init :";
  Hashtbl.iter (
    fun n vl -> printf " %a" Hstring.print n; 
      List.iter (printf "%a " print_value
      ) vl
  ) proc_init;
  printf "@."

let print_procninit () =
  printf "Proc_ninit : ";
  Hashtbl.iter (fun n _ -> printf " %a" Hstring.print n) proc_ninit;
  printf "@."


(* INITIALIZATION METHODS *)


(* Each type is associated to his constructors 
   The first one is considered as the default type *)
let init_types type_defs globals arrays =
  let upd_abst n =
    Hashtbl.add htbl_abstypes n (n, TI.empty);
  in
  List.iter (
    fun (t_name, t_fields) ->
      let fields = 
	if (List.length t_fields > 0)
	then (
	  List.fold_right (
	    fun field acc -> (Hstr field)::acc
	  ) t_fields []
	)
	else
	  (
	    let acc' =
	      List.fold_left (
		fun acc (n, ty) -> 
		  if ty = t_name 
		  then (
		    upd_abst n;
		    (Hstr n)::acc
		  ) else acc
	      ) [] globals in
	    List.fold_left (
	      fun acc (n, (_, ty)) -> 
		if ty = t_name 
		then (
		  upd_abst n;
		  (Hstr n)::acc
		) else acc
	    ) acc' arrays
	  )
      in
      Hashtbl.add htbl_types t_name fields
  ) type_defs
    
(* Initialization of the global variables to their
   default constructor, of the equivalence classes and
   of the difference classes *)
let init_globals globals =
  List.iter (
    fun (g_name, g_type) ->
      let t = 
	if Hashtbl.mem htbl_abstypes g_name then g_name else g_type in
      Hashtbl.add ec g_name (VVar g_name, RGlob t)
  ) globals

(* Initialization of the arrays with their default
   constructor (deterministic version) of the equivalence classes and
   of the difference classes *)
let init_arrays arrays =
  List.iter (
    fun (a_name, (a_dims, a_type)) ->
      let dims = List.length a_dims in
      let t = 
	if Hashtbl.mem htbl_abstypes a_name then a_name else a_type in
      Hashtbl.add ec a_name (VVar a_name, RArr (t, dims))
  ) arrays
    
(* Execution of the real init method from the cubicle file 
   to initialize the equivalence classes and difference classes *)
let init_htbls (vars, atoms) =
  List.iter (
    fun satom ->
      (* First look, equalities *)
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
		    let v = get_cvalue r in
		    ec_replace rep v
		  (* Var or Tab[] = Var or Tab[] *)
		  | (Elem (id1, Glob) | Access (id1, _)), (Elem (id2, Glob) | Access (id2, _)) ->
		    let (rep, st) as t1 = Hashtbl.find ec id1 in
		    let (rep' , st') as t2 = Hashtbl.find ec id2 in
		    (try let (rep, cfc) = Hashtbl.find htbl_abstypes id1 in 
			 abst_replace id2 rep cfc
		     with Not_found -> ()
		    );
		    let sr, dr =
		      match rep with
			| VVar _ -> rep', rep
			| _ -> rep, rep'
		    in ec_replace dr sr
		  | _ -> assert false
	      end
	    | _ -> () (* Will be handled during the second look *)
      ) satom;
      let i = Hstring.make "int" in
      let r = Hstring.make "real" in
      let cfc = ref 0 in
      Hashtbl.iter (
	fun n (rep, st) ->
	  try
	    let t = type_st st in
	    (* Abstract type *)
	    if n = t then raise Exit
	    else if (VVar n) = rep then
	      let ty, ts = 
		if Hstring.equal t i || Hstring.equal t r 
		then begin
		  let pv = Hashtbl.find htbl_types t in
		  let ts = List.fold_left (fun acc n -> TS.add n acc) TS.empty pv in
		  N, ts
		end
		else let vs = Hashtbl.find htbl_types t in
		     let ts' = List.fold_left (fun acc t -> TS.add t acc) TS.empty vs in
		     O, ts'
	      in
	      Hashtbl.add dc n (ty, ts, TI.empty, !cfc);
	      incr cfc
	  with Exit -> Hashtbl.replace ec n (Hstr n, st)
      ) ec;
      (* Second look, differences *)
      SAtom.iter (
	fun atom ->
	  match atom with
	    | Comp (t1, Eq, t2) -> () (* Already handled *)
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
			let (ty, ts, ti, cfc) = Hashtbl.find dc h in
			let v = get_cvalue c in
			let ts' = match ty with
			  | N -> TS.add v ts
			  | O -> TS.remove v ts 
			  | _ -> assert false
			in
			Hashtbl.replace dc h (ty, ts', ti, cfc)
		      with ConstrRep -> () (* Strange but allowed *)
		    end
		  (* Var or Tab[] <> Var or Tab[] *)
		  | (Elem (id1, Glob) | Access (id1, _)), (Elem (id2, Glob) | Access (id2, _)) ->
		    begin
		      (try let (rep, cfc) = Hashtbl.find htbl_abstypes id1 in
			   let (rep', cfc') = Hashtbl.find htbl_abstypes id2 in
			   abst_replace rep' rep' (TI.singleton rep);
			   abst_replace rep rep (TI.singleton rep')
		       with Not_found -> ()
		      );
		      let (rep1, _) = Hashtbl.find ec id1 in
		      let (rep2, _) = Hashtbl.find ec id2 in
		      match rep1, rep2 with
			| VVar h1, VVar h2 -> let (ty1, ts1, ti1, cfc1) = Hashtbl.find dc h1 in
					    let (ty2, ts2, ti2, cfc2) = Hashtbl.find dc h2 in
					    let cfc = min cfc1 cfc2 in
					    Hashtbl.replace dc h1 (ty1, ts1, TI.add h2 ti1, cfc);
					    Hashtbl.replace dc h2 (ty2, ts2, TI.add h1 ti2, cfc)
			| VVar h, (_ as rep') 
			| (_ as rep'), VVar h -> 	
			  let (ty, ts, ti, cfc) = Hashtbl.find dc h in
			  let ts' = match ty with
			    | N -> TS.add rep' ts
			    | O -> TS.remove rep' ts
			    | _ -> assert false in
			  Hashtbl.replace dc h (ty, ts', ti, cfc)
			| _ -> () (* Strange but that's your problem *)
		    end
		  | Elem (id, Glob), Elem (p, Var)
		  | Elem (p, Var), Elem (id, Glob) ->
		    let (rep, st) = Hashtbl.find ec id in
		    let h = match rep with VVar h -> h | _ -> assert false in
		    Hashtbl.remove dc h;
		    ec_replace rep fproc
		  | _ -> assert false
	      end 
	    | _ -> assert false
      ) satom
  ) atoms

let upd_options () =
  Hashtbl.iter
    ( fun n (rep, _) ->
      match rep with
	| VVar h when h <> n && Hashtbl.mem proc_init n -> Hashtbl.add proc_init h (Hashtbl.find proc_init n)
	| VVar h when h <> n && Hashtbl.mem proc_ninit n -> Hashtbl.add proc_ninit h ()
	| _ -> ()
    ) ec

let upd_init_list rep ts =
  let (_, st) = Hashtbl.find ec rep in
  Hashtbl.remove ec rep;
  (* Possible values according to the .sched file *)
  let pr = Hstring.make "proc" in
  let ts' = 
    match st with 
      | RGlob p | RArr (p, _) when p = pr ->
	if (init_proc && not (Hashtbl.mem proc_ninit rep))
	then (
	  TS.union (TS.singleton (TS.min_elt ts)) (TS.singleton fproc)
	) else if not init_proc && Hashtbl.mem proc_init rep
	  then
	    let l = Hashtbl.find proc_init rep in
	    List.fold_left (
	      fun acc i -> TS.add i acc
	    ) TS.empty l
	  else TS.singleton (TS.min_elt ts)
      | _ -> ts
  in
  let ce = Hashtbl.fold (
    fun n (rep', st) acc ->
      if (VVar rep) = rep' 
      then (
	Hashtbl.remove ec n;
	(n, st) :: acc )
      else acc
  ) ec [] in
  init_list := (rep, st, ts', ce) :: !init_list
    
let upd_inits () =
  let dc' = Hashtbl.copy dc in
  Hashtbl.iter (
    fun rep (ty, ts, ti, cfc) ->
      let tis = Hashtbl.fold (
	fun rep' (ty', ts', ti', cfc') acc ->
	  if cfc = cfc'
	  then (
	    Hashtbl.remove dc' rep';
	    TIS.add (rep', ts', ti') acc
	  ) else acc
      ) dc' TIS.empty in
      if TIS.cardinal tis = 1 
      then upd_init_list rep ts
      else Hashtbl.add inits cfc tis
  ) dc'

let graph_coloring () =
  let rec color ucl cl =
    match ucl with
      | [] -> cl
      | (rep, ts, ti)::tl -> 
	let ts' = List.fold_left (
	  fun acc (crep, _, c, _) -> 
	    if TI.mem crep ti 
	    then TS.diff acc c
	    else acc
	) ts cl in
	let c = TS.min_elt ts' in
	let (_, st) = try Hashtbl.find ec rep with Not_found -> printf "Error %a" Hstring.print rep; exit 1 
	in
	Hashtbl.remove ec rep;
	let ce = Hashtbl.fold (
	  fun n (rep', st) acc ->
	    if (VVar rep) = rep' 
	    then (
	      Hashtbl.remove ec n;
	      (n, st) :: acc )
	    else acc
	) ec [] in
	color tl ((rep, st, TS.singleton c, ce)::cl)	
  in
  Hashtbl.iter (
    fun _ tis ->
      let q = TIS.elements tis in
      let il = color q [] in
      init_list := il @ !init_list
  ) inits

let fill_ntv () = 			
  Hashtbl.iter 			
    (fun h (_, t) -> 			
      Hashtbl.add ntValues h (Hashtbl.find htbl_types (hst t)) 			
    ) ec 
	    
let initialization init =
  init_htbls init;
  upd_options ();
  fill_ntv ();
  upd_inits ();
  graph_coloring ();
  let etati = Etat.init () in
  let c = ref 0 in
  let upd_etati n (v, tself) =
    match tself with
      | RGlob _ -> Etat.set_v etati n v
      | RArr (_, d) -> let tbl =
  			 try let al = Hashtbl.find tab_init n in
			     Array.minit d nb_threads al v
  			 with Not_found -> Array.init d nb_threads v
  		       in
  		       Etat.set_a etati n tbl
  in		       
  let upd_init () =
    incr c;
    let i = Etat.copy etati in
    let tr = Hstring.make ("init" ^ (string_of_int !c)) in
    sinits := Syst.add i [(tr, [])] !sinits
  in
  let rec create_init l =
    match l with
      | [(rep, st, vts, oth)] ->
  	TS.iter (
	  fun v ->
	    List.iter (fun (n, tn) -> upd_etati n (v, tn)) oth;
	    upd_etati rep (v, st);
	    upd_init ()
	) vts
      | (rep, st, vts, oth) :: tl ->
  	TS.iter (
	  fun v ->
	    List.iter (fun (n, tn) -> upd_etati n (v, tn)) ((rep, st)::oth);
	    create_init tl
	) vts
      | _ -> upd_init ()
  in
  Hashtbl.iter upd_etati ec;
  create_init !init_list;
  printf "Nb init states : %d@." (Syst.cardinal (!sinits))


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
		 Etat.set_v !write_st var value)::acc
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
		    let v = get_value s term in
		    Etat.set_e !write_st u.up_arr pl v
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
  initialization se.init;
  Hashtbl.clear ec;
  Hashtbl.clear dc;
  Hashtbl.clear inits;
  init_list := []

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
	    let pn = List.fold_right (
	      fun (id, i) pn -> 
		let si = string_of_int i in
		let p = Hstring.make ("#" ^ si) in
	        p :: pn
	    ) sub [] in
	    (tr.tr_name, pn, subst_guard, subst_ureq, subst_updates)::acc'
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

module TSet = Set.Make (
  struct
    type t = Hstring.t
    let compare = Hstring.compare
  end
)

let pTrans = ref TSet.empty
let tTrans = ref TSet.empty
let ntTrans = ref TSet.empty
let iTrans = ref TSet.empty

let valid_trans_list () =
  (* let compare _ _ = if Random.bool () then -1 else 1 in *)
  List.fold_left (
    fun acc (name, pn, req, ureq, updts) -> 
      if valid_req req && valid_ureq ureq 
      then
	(
	  pTrans := TSet.add name !pTrans;
	  ((name, pn), updts) :: acc
	)
      else acc
  ) [] !trans_list
    
(* SYSTEM UPDATE *)


let rec update_system_alea c =
  if c = nb_exec then c
  else
    let trl = Syst.find !read_st !system in
    let tlist = ref (valid_trans_list ()) in
    let i = Random.int (List.length !tlist) in
    let (((tr, args) as trn), (assigns, updates)) = List.nth !tlist i in
    List.iter (fun a -> a ()) assigns;
    let updts = valid_upd updates in 
    List.iter (fun us -> List.iter (fun u -> u ()) us ) updts;
    let s = Etat.copy !write_st in
    system := Syst.add s (trn::trl) !system;
    tTrans := TSet.add tr !tTrans;
    read_st := s;
    update_system_alea (c+1)

 let compare ((n1, pn1), _) ((n2, pn2), _) =
    if TSet.mem n1 !tTrans && not (TSet.mem n2 !tTrans) then 1
    else if not (TSet.mem n1 !tTrans) && TSet.mem n2 !tTrans then -1
    (* else if np1 > np2 then -1 *)
    (* else if np1 < np2 then 1 *)
    else if Random.bool () then -1 else 1

let rec find_and_exec_gt =
  function
    | [] -> raise Exit
    | (t, (assigns, updates)) :: tl ->
      List.iter (fun a -> a ()) assigns;
      let updts = valid_upd updates in
      List.iter (fun us -> List.iter (fun u -> u ()) us) updts;
      if Syst.mem !write_st !system then
	find_and_exec_gt tl
      else (t, tl)

let rec update_system_noc c rs tlist parents =
  if c = nb_exec then c
  else
    try 
      read_st := rs;
      write_st := Etat.copy rs;
      let ((tr, _) as trn, tlist') = find_and_exec_gt tlist in
      let trl = try Syst.find !read_st !system
	with Not_found -> printf "Error state :@.";
	  print_state !read_st; 
	  exit 1
      in
      let s = Etat.copy !write_st in
      system := Syst.add s (trn::trl) !system;
      tTrans := TSet.add tr !tTrans;
      let wtlist = valid_trans_list () in
      update_system_noc (c+1) s wtlist ((rs, tlist')::parents)
    with Exit -> match parents with 
      | [] -> raise (TEnd c)
      | (rs, tlist) :: tl -> update_system_noc c rs tlist tl

let update_system_width c rs tlist =
  let to_do = Queue.create () in
  Queue.add (0, rs, tlist, []) to_do;
  system := Syst.add rs [] !system;
  while not (Queue.is_empty to_do) do
    let depth, rs, tlist, trn = Queue.take to_do in
    if depth <= c then
      (
	read_st := rs;
	write_st := Etat.copy rs;
	List.iter (
	  fun (((tr, _) as t), (assigns, updates)) ->
	    List.iter (fun a -> a ()) assigns;
	    let updts = valid_upd updates in
	    List.iter (fun us -> List.iter (fun u -> u ()) us) updts;
	    let nst = Etat.copy !write_st in
	    if not (Syst.mem nst !system) then
	      (
		
		tTrans := TSet.add tr !tTrans;
		let trn' = t::trn in
      		system := Syst.add nst trn' !system;
		let tlist = valid_trans_list () in
		Queue.add (depth + 1, nst, tlist, trn') to_do
	      )
	) tlist
      )
  done;
  c
	    
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
    fun state _ ->
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
  ) !system
    
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
  init_system se;
  init_transitions se.trans;
  let trans = List.fold_left (fun acc (n, _, _, _, _) -> TSet.add n acc) TSet.empty !trans_list in
  let nb_ex = nb_exec 
  (* if nb_exec > 0 then nb_exec *)
  (* else 4 *)
  (* let acc = List.fold_left ( *)
  (* 	fun acc (n, ty) -> *)
  (* 	  acc * (List.length (try Hashtbl.find htbl_types ty *)
  (* 	    with Not_found -> Hashtbl.find htbl_types n) *)
  (* )) 1 se.globals  *)
  (* in *)
  (* List.fold_left ( *)
  (* 	fun acc' (n, (_,ty)) -> *)
  (* 	  acc' * (List.length (try Hashtbl.find htbl_types ty *)
  (* 	    with Not_found -> Hashtbl.find htbl_types n) *)
  (* 	  )) acc se.arrays  *)
  in
  printf "Nb exec : %d@." nb_ex;
  Syst.iter (
    fun st tri ->
      (* printf "Beginning@."; *)
      read_st := st;
      write_st := Etat.copy st;
      system := Syst.add st tri !system;
      (* printf "Init state :@."; *)
      (* print_state s; *)
      try
	ignore (
	  if upd = 0 then
	    let tlist = valid_trans_list () in
	    update_system_noc 0 st tlist []
	  else if upd = 1 then
	    let tlist = valid_trans_list () in
	    update_system_width forward_depth st tlist
	  else
	    update_system_alea 0
	)
      (* printf "Normal end : %d" c *)
      with TEnd i -> printf "Prematured end : %d" i
  ) !sinits;
  ntTrans := TSet.diff !pTrans !tTrans;
  iTrans := TSet.diff trans !pTrans;
  printf "Scheduled %d states\n" (Syst.cardinal (!system));
  printf "--------------------------@.";
  if verbose > 0 then
    (
      if (TSet.cardinal !ntTrans > 0) then
	(
	  printf "Not taken but seen transitions :@.";
	  TSet.iter (printf "\t%a@." Hstring.print) !ntTrans
	) else (printf "All transitions that were seen were taken !@.");
      if (TSet.cardinal !iTrans > 0) then
	(
	  printf "Not seen transitions :@.";
	  TSet.iter (printf "\t%a@." Hstring.print) !iTrans
	) else (printf "All transitions were seen !@.");
    );
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
  (* system := Syst.empty; *)
  sinits := Syst.empty;
  read_st := Etat.init ();
  write_st := Etat.init ();
  tTrans := TSet.empty;
  pTrans := TSet.empty;
  scheduler !current_system
