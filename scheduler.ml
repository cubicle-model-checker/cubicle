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
      Parser.scheduler Lexer.token lb;
    with 
	Parsing.Parse_error ->
	  let  loc = (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb) in
	  report loc file;
          printf "\nsyntax error\n@.";
	  exit 2
  with Exit -> ()
    
let init_proc = !init_proc
let prio_list = !prio_list

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

type transition = 
    {
      t_grp : int;
      t_name : Hstring.t;
      t_args : Hstring.t list;
      t_reqs : (unit -> bool) list;
      t_ureqs : (unit -> bool) list list list;
      t_assigns : (unit -> unit) list;
      t_updates : ((unit -> bool) list * (unit -> unit)) list list list;
    }

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

module type RC = sig

  exception SizeError of int
  exception BadPercentage of int
      
  type elt
  type t

  val init : int list -> t
  val add : int -> elt -> t -> t
  val choose : t -> elt
  val update : t -> t
  val print_rc : t -> unit

end

module RandClasses : RC with type elt = transition = struct
    
  exception SizeError of int
  exception BadPercentage of int

  type elt = transition

  module C : Map.S with type key = int = Map.Make (
    struct type t = int 
	   let compare = Pervasives.compare 
    end)

  type t = {rc : (int * (int * int) * (elt C.t)) list; sum : int}

  let init bl =
    let g = List.length bl in
    let rec init' acc l ti =
      match l with
  	| [] -> if ti <> 100 then raise (BadPercentage ti) else acc
  	| p :: tl ->
	  let bsup = p + ti in
	  if bsup > 100 then raise (BadPercentage (bsup))
	  else (
	    let g' = g - List.length l in
	    let acc = (g', (ti, bsup), C.empty) :: acc in
  	    init' acc tl (p + ti)
	  )
    in 
    let nc = match bl with
      | [] -> [(-1, (0,100), C.empty)]
      | _ -> init' [] bl 0 
    in
    {rc = List.rev nc; sum = 100}

  let add i e rc =
    if i >= List.length rc.rc then raise (SizeError i)
    else  
      let rec add' acc rc = 
	match rc with
	  | ((i', _, _) as hd)::tl when i' <> i -> add' (hd::acc) tl
	  | (i, b, c)::tl -> let l = C.cardinal c in
			     (List.rev acc)@((i, b, C.add l e c)::tl)
	  | _ -> assert false
      in
      let nrc = add' [] rc.rc in
      {rc = nrc; sum = 100}

  let choose rc =
    let r = Random.int rc.sum in
    let (_, _, c) = try
		      List.find (fun (_, (binf, bsup), c) -> r >= binf && r < bsup) rc.rc
      with Not_found -> Format.eprintf "Not found %d" r; exit 1
    in
    let i = Random.int (C.cardinal c) in
    C.find i c

  let update rc =
    let (nrc, sum) = List.fold_left (
      fun ((nrc, sum) as acc) ((_, (binf, bsup), c) as e) ->
	if C.is_empty c then acc else (e::nrc, sum + (bsup - binf))
    ) ([], 0) rc.rc in
    let (_, nrc) = List.fold_right ( 
      fun (i, (binf, bsup), c)  (pbi, acc) ->
	let bsup = pbi + bsup - binf in
	(bsup, (i, (pbi, bsup), c) :: acc)
    ) nrc (0, []) in
    {rc = List.rev nrc; sum = sum}

  let print_rc rc =
    List.iter (fun (i, (bi, bs), c) -> 
      Format.printf "%d : %d -> %d \n   {" i bi bs;
      C.iter (fun i t -> Format.printf "\n\t#%d - %a(%a)"
	i Hstring.print t.t_name (Hstring.print_list " ") t.t_args) c;
      Format.printf "\n   }@."
    ) rc.rc;
    Format.printf "sum : %d@." rc.sum

end    

 (* This list will contain all the transitions *)
let trans_list = ref []
let trans_rc = ref (RandClasses.init prio_list)

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


let print_time fmt sec =
  let minu = floor (sec /. 60.) in
  let extrasec = sec -. (minu *. 60.) in
  fprintf fmt "%dm%2.3fs" (int_of_float minu) extrasec

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
  ) var_init;
  printf "@."

let print_procninit () =
  printf "Proc_ninit : ";
  Hashtbl.iter (fun n _ -> printf " %a" Hstring.print n) var_ninit;
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
	| VVar h when h <> n && Hashtbl.mem var_init n -> Hashtbl.add var_init h (Hashtbl.find var_init n)
	| VVar h when h <> n && Hashtbl.mem var_ninit n -> Hashtbl.add var_ninit h ()
	| _ -> ()
    ) ec

let upd_init_list rep ts =
  let (_, st) = Hashtbl.find ec rep in
  Hashtbl.remove ec rep;
   (* Possible values according to the .sched file *)
  let ts' = 
    if (init_proc && not (Hashtbl.mem var_ninit rep))
    then (
      TS.union (TS.singleton (TS.min_elt ts)) (TS.singleton fproc)
    ) else if not init_proc && Hashtbl.mem var_init rep
      then
	(
	  let l = Hashtbl.find var_init rep in
	  List.fold_left (
	    fun acc i -> TS.add i acc
	  ) TS.empty l
	)
      else (
	TS.singleton (TS.min_elt ts)
      )
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
  let ub = List.length prio_list - 1 in
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
	    let subst_req = substitute_req sub tr.tr_reqs in
	    let (s_assigns, s_updates) = substitute_updts sub tr.tr_assigns tr.tr_upds in
	    let pn = List.fold_right (
	      fun (id, i) pn -> 
		let si = string_of_int i in
		let p = Hstring.make ("#" ^ si) in
		p :: pn
	    ) sub [] in
	    let grp = try Hashtbl.find trans_prio tr.tr_name 
	      with Not_found -> ub
	    in
	    let t = 
	      { t_grp = grp;
		t_name = tr.tr_name;
		t_args = pn;
		t_reqs = subst_req;
		t_ureqs = subst_ureq;
		t_assigns = s_assigns;
		t_updates = s_updates
	      } in
	    t::acc'
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

let valid_trans req ureq = valid_req req && valid_ureq ureq

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

module TMap = Map.Make (
  struct
    type t = Hstring.t
    let compare = Hstring.compare
  end
)

let trans = ref TMap.empty
let execTrans = ref TMap.empty

let valid_trans_rc () =
  let rc = List.fold_left (
    fun acc t -> 
      if valid_trans t.t_reqs t.t_ureqs
      then
	(
	  if profiling then
	    (
	      let n = TMap.find t.t_name !trans in
	      trans := TMap.add t.t_name (n+1) !trans
	    );
	  Search.TimerRC.start ();
	  let nacc = RandClasses.add t.t_grp t acc in
	  Search.TimerRC.pause ();
	  nacc
	)
      else acc
  ) !trans_rc !trans_list in
  RandClasses.update rc


let valid_trans_list () =
  List.fold_left (
    fun acc t -> 
      if valid_trans t.t_reqs t.t_ureqs
      then
	(
	  if profiling then
	    (
	      let n = TMap.find t.t_name !trans in
	      trans := TMap.add t.t_name (n+1) !trans
	    );
	  t :: acc
	)
      else acc
  ) [] !trans_list

 (* SYSTEM UPDATE *)

let rec update_system_alea rs trl c =
  if c = nb_exec then ()
  else
    (
      try
	read_st := rs;
	let rc = valid_trans_rc () in
	let t = RandClasses.choose rc in
	List.iter (fun a -> a ()) t.t_assigns;
	let updts = valid_upd t.t_updates in 
	List.iter (fun us -> List.iter (fun u -> u ()) us ) updts;
	let s = Etat.copy !write_st in
	let trl' = (t.t_name,t.t_args)::trl in
	system := Syst.add s trl' !system;
	if profiling then
	  (
	    let n = TMap.find t.t_name !execTrans in
	    execTrans := TMap.add t.t_name (n+1) !execTrans
	  );
	update_system_alea s trl' (c+1)
      with Invalid_argument _ -> ()
    )

 (* let compare ((n1, pn1), _) ((n2, pn2), _) = *)
 (*   if TMap.mem n1 !execTrans && not (TMap.mem n2 !execTrans) then 1 *)
 (*   else if not (TMap.mem n1 !execTrans) && TMap.mem n2 !execTrans then -1 *)
 (*   (\* else if np1 > np2 then -1 *\) *)
 (*   (\* else if np1 < np2 then 1 *\) *)
 (*   else if Random.bool () then -1 else 1 *)

 (* let rec find_and_exec_gt = *)
 (*   function *)
 (*     | [] -> raise Exit *)
 (*     | t :: tl -> *)
 (*       List.iter (fun a -> a ()) t.t_assigns; *)
 (*       let updts = valid_upd t.t_updates in *)
 (*       List.iter (fun us -> List.iter (fun u -> u ()) us) updts; *)
 (*       if Syst.mem !write_st !system then *)
 (* 	find_and_exec_gt tl *)
 (*       else (t, tl) *)

 (* let rec update_system_dfs c workst parents = *)
 (*   if c = nb_exec then () *)
 (*   else *)
 (*     try  *)
 (*       let (tlist, parents) = *)
 (* 	match workst with *)
 (* 	  | Some rs -> read_st := rs; *)
 (* 	    (valid_trans_list (), parents); *)
 (* 	  | None -> match parents with *)
 (* 	      | [] -> raise (TEnd c) *)
 (* 	      | (rs, tli) :: tl -> read_st := rs; *)
 (* 		(tli, tl) *)
 (*       in *)
 (*       write_st := Etat.copy (!read_st); *)
 (*       let (t, tlist') = find_and_exec_gt tlist in *)
 (*       let trl = Syst.find !read_st !system in *)
 (*       let s = Etat.copy !write_st in *)
 (*       system := Syst.add s ((t.t_name, t.t_args)::trl) !system; *)
 (*       let n = TMap.find t.t_name !execTrans in *)
 (*       execTrans := TMap.add t.t_name (n+1) !execTrans; *)
 (*       update_system_dfs (c+1) (Some s) ((!read_st, tlist')::parents) *)
 (*     with Exit -> update_system_dfs c None parents *)

let cpt_f = ref 0

let update_system_bfs c rs =
  let cpt_q = ref 1 in
  let to_do = Queue.create () in
  let trl = Syst.find rs !system in
  Queue.add (1, rs, trl) to_do;
  while not (Queue.is_empty to_do) do
    let depth, rs, trn = Queue.take to_do in
    incr cpt_f;
    decr cpt_q;
    if depth <= c then
      (
	if not quiet && !cpt_f mod 1000 = 0 then
	  eprintf "%d (%d)@." !cpt_f !cpt_q;
	read_st := rs;
	let tlist = valid_trans_list () in
	List.iter (
	  fun t ->
	    if profiling then
	      (
		let n = TMap.find t.t_name !execTrans in
		execTrans := TMap.add t.t_name (n+1) !execTrans
	      );
	    write_st := Etat.copy rs;
	    List.iter (fun a -> a ()) t.t_assigns;
	    let updts = valid_upd t.t_updates in
	    List.iter (fun us -> List.iter (fun u -> u ()) us) updts;
	    let nst = Etat.copy !write_st in
	    if not (Syst.mem nst !system) then
	      (
		incr cpt_q;
		let trn' = (t.t_name, t.t_args)::trn in
		system := Syst.add nst trn' !system;
		Queue.add (depth + 1, nst, trn') to_do
	      )
	) tlist
      )
  done

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

let hist_cand cand =
  try
    let (pl, sa) = cand.t_unsafe in
    let subst = Ast.all_permutations pl list_threads in
    let good = Syst.filter (
      fun st _ -> 
	List.exists (
	  fun sub ->
	    SAtom.for_all (
	      fun a ->
		match a with
		  | True -> true
		  | False -> false
		  | Comp (t1, op, t2) -> 
		    let t1_v = get_value_st sub st t1 in
		    let t2_v = get_value_st sub st t2 in
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
	) subst
    ) !system in
    printf "Number of good states %d@." (Syst.cardinal good);
    let gs = ref (Syst.choose good) in
    Syst.iter (
      fun st' trn' -> if List.length trn' < List.length (snd !gs) then gs := (st', trn')
    ) good;
    !gs
  with Not_found -> printf "HIST CAND@."; exit 1
 (* MAIN *)


let scheduler se =
  Search.TimerScheduler.start ();
  Syst.iter (
    fun st tri ->
      read_st := st;
      write_st := Etat.copy st;
      system := Syst.add st tri !system;
      try
	if upd = 2 then
	  (
	    decr cpt_f;
	    update_system_bfs forward_depth st
	  )
	else
	  update_system_alea st tri 0
      with TEnd i -> printf "Prematured end : %d" i
  ) !sinits;
  Search.TimerScheduler.pause ()


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

let init_sched () =
  init_system !current_system;
  init_transitions (!current_system).trans;
  if profiling then
    List.iter (
      fun t -> 
	trans := TMap.add t.t_name 0 !trans;
	execTrans := TMap.add t.t_name 0 !execTrans
    ) !trans_list

let run () = 
  try
    assert (!current_system <> dummy_system);
    read_st := Etat.init ();
    write_st := Etat.init ();
    init_sched ();
    let runs = if upd = 2 then 1 else runs in
    for i = 1 to runs do 
      if i mod 100 = 0 
      then printf "Execution #%d : nb_st : %d@." 
	i (Syst.cardinal !system);
      ignore (scheduler !current_system) 
    done;
    if profiling then
      (
	let inits = float_of_int (Syst.cardinal (!sinits)) in
	let nb_ex = 
	  if upd = 2 then float_of_int !cpt_f 
	  else float_of_int runs *. inits *. float_of_int nb_exec in
	printf "Nb exec : %.0f@." nb_ex;
	let (etl, netl) = TMap.fold (
	  fun t i (etl, netl) ->
	    if i > 0 then
	      let fi = float_of_int i in
	      let p = TMap.find t !trans in
	      let fp = float_of_int p in
	      ((t, fp /. nb_ex *. 100., p, fi /. nb_ex *. 100., fi /. fp *. 100., i) :: etl, netl)
	    else (etl, t::netl)
	) !execTrans ([], []) in
	let etl = List.fast_sort (
	  fun (_, _, _, p, _, _) (_, _, _,p', _, _) -> - Pervasives.compare p p'
	) etl in
	let etl' = List.fast_sort (
	  fun (_, _, _, _, p, _) (_, _, _, _, p', _) -> - Pervasives.compare p p'
	) etl in
	let etl'' = List.fast_sort (
	  fun (_, p, _, _, _, _) (_, p', _, _, _, _) -> - Pervasives.compare p p'
	) etl in
      (* printf "Seen transitions :@."; *)
      (* List.iter ( *)
      (* 	fun (t, p) -> printf "\t%-26s : %5.2f%%@." (Hstring.view t) p *)
      (* ) tl; *)
	printf "Executed transitions :@.";
	printf "\n\t%-26s | %8s | %8s | %8s | %8s | %8s\n@." "Transitions" "vues/tot" "vues" "EXEC/TOT" "exec/vues" "exec";
	List.iter (
	  fun (t, p, i, p', p'', i') -> printf "\t%-26s | %7.2f%% | %8d | %7.2f%% | %8.2f%% | %8d@." (Hstring.view t) p i p' p'' i'
	) etl; 
	printf "\n\t%-26s | %8s | %8s | %8s | %8s | %8s\n@." "Transitions" "vues/tot" "vues" "exec/tot" "EXEC/VUES" "exec";
	List.iter (
	  fun (t, p, i, p', p'', i') -> printf "\t%-26s | %7.2f%% | %8d | %7.2f%% | %8.2f%% | %8d@." (Hstring.view t) p i p' p'' i'
	) etl';
	printf "\n\t%-26s | %8s | %8s | %8s | %8s | %8s\n@." "Transitions" "VUES/TOT" "vues" "exec/tot" "exec/vues" "exec";
	List.iter (
	  fun (t, p, i, p', p'', i') -> printf "\t%-26s | %7.2f%% | %8d | %7.2f%% | %8.2f%% | %8d@." (Hstring.view t) p i p' p'' i'
	) etl'';
      (* if (TMap.cardinal !notExecTrans > 0) then *)
      (* 	( *)
      (* 	  printf "Not taken but seen transitions :@."; *)
      (* 	  TMap.iter (printf "\t%a : %d@." Hstring.print) !notExecTrans *)
      (* 	) else (printf "All transitions that were seen were taken !@."); *)
      (* if (TMap.cardinal !notSeenTrans > 0) then *)
      (* 	( *)
      (* 	  printf "Not seen transitions :@."; *)
      (* 	  TMap.iter (printf "\t%a : %d@." Hstring.print) !notSeenTrans *)
      (* 	) else (printf "All transitions were seen !@."); *)
	printf "--------------------------@.";
      );
    printf "Total scheduled states : %d
 --------------------------------\n@." (Syst.cardinal !system);
    if verbose > 1 && not quiet then
      begin
	let count = ref 1 in
	Syst.iter (
  	  fun st -> 
	    printf "%d : " !count; 
	    incr count; 
	    print_system st
	) (!system)
      end
  with Not_found -> printf "RUN@."; exit 1

