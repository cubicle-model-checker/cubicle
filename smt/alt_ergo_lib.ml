(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
module AE = AltErgo
module WPT = AE.Why_ptree
module SAT = (val (AE.Sat_solvers.get_current ()) : AE.Sat_solvers.S)
module FE = AE.Frontend.Make(SAT)

let hsca chs = AE.Hstring.make (Hstring.view chs)
let hsac ahs = Hstring.make (AE.Hstring.view ahs)
let lhsca lchs = List.map hsca lchs
let lhsac lahs = List.map hsac lahs
       
let dl = (Lexing.dummy_pos, Lexing.dummy_pos)
       
type error = 
  | DuplicateTypeName of Hstring.t
  | DuplicateSymb of Hstring.t
  | UnknownType of Hstring.t
  | UnknownSymb of Hstring.t

exception Error of error

type check_strategy = Lazy | Eager
                      
module H = Hstring.H
module HSet = Hstring.HSet

let all_events = ref []
let formula = ref []

let decl_types = H.create 17
let decl_symbs = H.create 17

let htrue = Hstring.make "True"
let hfalse = Hstring.make "False"

module Type = struct

  type t = Hstring.t

  let equal = Hstring.equal

  let type_int = 
    let tint = Hstring.make "int" in
    H.add decl_types tint AE.Ty.Tint;
    tint

  let type_real = 
    let treal = Hstring.make "real" in
    H.add decl_types treal AE.Ty.Treal;
    treal

  let type_bool = 
    let tbool = Hstring.make "bool" in
    H.add decl_types tbool AE.Ty.Tbool;
    tbool

  let type_proc = 
    let tproc = Hstring.make "proc" in
    H.add decl_types tproc AE.Ty.Tint;
    tproc

  let type_weak =
    Hstring.make "_weak_var"
      
  let type_event =
    Hstring.make "_event"

  let declare_constructor ty c = 
    if H.mem decl_symbs c then raise (Error (DuplicateSymb c));
    H.add decl_symbs c 
      (AE.Symbols.name ~kind:AE.Symbols.Constructor (Hstring.view c), [], ty)

  let declare t constrs =
    if H.mem decl_types t then raise (Error (DuplicateTypeName t));
    match constrs with
      | [] ->
          H.add decl_types t (AE.Ty.Text ([], hsca t))
      | _ -> 
	  let ty = AE.Ty.Tsum (hsca t, lhsca constrs) in
	  H.add decl_types t ty;
	  List.iter (fun c -> declare_constructor t c) constrs

  let all_constructors () =
    H.fold (fun _ c acc -> match c with
      | AE.Symbols.Name (h, AE.Symbols.Constructor), _, _ -> (hsac h) :: acc
      | _ -> acc
    ) decl_symbs [htrue; hfalse]

  let constructors ty =
    if Hstring.equal ty type_bool then [htrue; hfalse]
    else match H.find decl_types ty with
      | AE.Ty.Tsum (_, cstrs) -> lhsac cstrs
      | _ -> []

  let declared_types () =
    H.fold (fun ty _ acc -> ty :: acc) decl_types []

  let type_direction =
    let tdir = Hstring.make "_direction" in
    let cdir = [ Hstring.make "_R" ; Hstring.make "_W" ] in
    declare tdir cdir;
    tdir

  let declare_event_type wvl =
    let cwv = List.map (fun wv ->
      Hstring.make ("_V" ^ (Hstring.view wv))) wvl in
    declare type_weak cwv;

    let fevent = [ (AE.Hstring.make "tid", AE.Ty.Tint) ;
		   (AE.Hstring.make "dir", H.find decl_types type_direction) ;
		   (AE.Hstring.make "loc", H.find decl_types type_weak) ;
		   (AE.Hstring.make "val", AE.Ty.Tint) ] in
    let tyevent = AE.Ty.Trecord { AE.Ty.args = [];
				  AE.Ty.name = hsca type_event;
				  AE.Ty.lbs = fevent } in
    H.add decl_types type_event tyevent

end

module Symbol = struct
    
  type t = Hstring.t

  let declare ?(weak=false) f args ret =
    if H.mem decl_symbs f then raise (Error (DuplicateTypeName f));
    List.iter 
      (fun t -> 
	if not (H.mem decl_types t) then raise (Error (UnknownType t)) )
      (ret::args);
    H.add decl_symbs f (AE.Symbols.name (Hstring.view f), args, ret)

  let type_of s = let _, args, ret = H.find decl_symbs s in args, ret

  let is_weak s =
    try snd (type_of (Hstring.make ("_V" ^ Hstring.view s))) = Type.type_weak
    with Not_found -> false

  let declared s = 
    let res = H.mem decl_symbs s in
    if not res then begin 
      eprintf "Not declared : %a in@." Hstring.print s;
      H.iter (fun hs (sy, _, _) ->
	eprintf "%a (=?%b) -> %a@." Hstring.print hs 
	  (Hstring.compare hs s = 0)
	  AE.Symbols.print sy)
	  decl_symbs;
      end;
      res

  let not_builtin ty = Hstring.equal ty Type.type_proc ||
    not (Hstring.equal ty Type.type_int || Hstring.equal ty Type.type_real ||
	   Hstring.equal ty Type.type_bool || Hstring.equal ty Type.type_proc)
    
  let has_abstract_type s =
    let _, ret = type_of s in
    match H.find decl_types ret with
      | AE.Ty.Text _ -> true
      | _ -> false

  let has_infinite_type s =
    let _, ret = type_of s in
    Hstring.equal ret Type.type_real ||
    Hstring.equal ret Type.type_int ||
    (* Hstring.equal ret Type.type_proc || *)
    match H.find decl_types ret with
      | AE.Ty.Text _ -> true
      | _ -> false
     
  let has_type_proc s =
    Hstring.equal (snd (type_of s)) Type.type_proc
      
  let _ = 
    H.add decl_symbs htrue (AE.Symbols.True, [], Type.type_bool);
    H.add decl_symbs hfalse (AE.Symbols.False, [], Type.type_bool);
    
end


module Variant = struct
    
  let constructors = H.create 17
  let assignments = H.create 17

  let find t x = try H.find t x with Not_found -> HSet.empty
    
  let add t x v = 
    let s = find t x in
    H.replace t x (HSet.add v s)
      
  let assign_constr = add constructors
    
  let assign_var x y = 
    if not (Hstring.equal x y) then
      add assignments x y
	
  let rec compute () = 
    let flag = ref false in
    let visited = ref HSet.empty in
    let rec dfs x s = 
      if not (HSet.mem x !visited) then
	begin
	  visited := HSet.add x !visited;
	  HSet.iter 
	    (fun y -> 
	      let c_x = find constructors x in
	      let c_y = find constructors y in
	      let c = HSet.union c_x c_y in
	      if not (HSet.equal c c_x) then
		begin
		     H.replace constructors x c;
		     flag := true
		end;
	      dfs y (find assignments y)
	    ) s
	end
    in
    H.iter dfs assignments;
    if !flag then compute ()
      
  let hset_print fmt s = 
    HSet.iter (fun c -> Format.eprintf "%a, " Hstring.print c) s
      
  let print () =
    H.iter 
      (fun x c -> 
         Format.eprintf "%a : %a = {%a}@."
           Hstring.print x
           Hstring.print (snd (Symbol.type_of x))
           hset_print c) 
      constructors

  let get_variants = H.find constructors
    
  let set_of_list = List.fold_left (fun s x -> HSet.add x s) HSet.empty 
    
  let init l = 
    compute ();
    List.iter 
      (fun (x, nty) -> 
	if not (H.mem constructors x) then
	  let ty = H.find decl_types nty in
	  match ty with
	    | AE.Ty.Tsum (_, l) ->
	        H.add constructors x (set_of_list (lhsac l))
	    | _ -> ()) l;
    H.clear assignments

  let update_decl_types s old_ty x =
    let new_ty = Hstring.(view old_ty ^ "_" ^ view x |> make) in
    let l = HSet.elements s in
    let ty = AE.Ty.Tsum (hsca new_ty, (* List.rev *) (lhsca l)) in
    H.replace decl_types new_ty ty;
    new_ty

  let close () = 
    compute ();
    H.iter 
      (fun x s -> 
	let sy, args, old_ty = H.find decl_symbs x in
	let nty = update_decl_types s old_ty x in
	H.replace decl_symbs x (sy, args, nty))
      constructors
      
end

module Term = struct

  type t = AE.Term.t
  type operator = Plus | Minus | Mult | Div | Modulo

  let make_int i = AE.Term.int (Num.string_of_num i)

  let make_real r = AE.Term.real (Num.string_of_num r)

  let make_app s l =
    try
      let (sb, _, nty) = H.find decl_symbs s in
      let ty = H.find decl_types nty in
      AE.Term.make sb l ty
    with Not_found -> raise (Error (UnknownSymb s))

  let t_true = AE.Term.vrai
  let t_false = AE.Term.faux

  let make_arith op t1 t2 = 
    let op =
      match op with
	| Plus -> AE.Symbols.Plus
	| Minus -> AE.Symbols.Minus
	| Mult ->  AE.Symbols.Mult
	| Div -> AE.Symbols.Div
	| Modulo -> AE.Symbols.Modulo
    in
    let ty = 
      if AE.Term.is_int t1 && AE.Term.is_int t2 then AE.Ty.Tint
      else if AE.Term.is_real t1 && AE.Term.is_real t2 then AE.Ty.Treal
      else assert false
    in
    AE.Term.make (AE.Symbols.Op op) [t1; t2] ty

  let make_eventid_field ?(qv=false) eid f =
    let ty = match f with
      | "tid" -> AE.Ty.Tint
      | "dir" -> H.find decl_types Type.type_direction
      | "loc" -> H.find decl_types Type.type_weak
      | "val" -> AE.Ty.Tint (*
	 let ev = (fst e.Event.var) in
	 let (_, _, nty) = H.find decl_symbs ev in
	 try H.find decl_types nty
	 with Not_found -> raise (Error (UnknownSymb ev)) *)
      | _ -> failwith "Alt_ergo_lib.Term.make_eventid_field : bad field name"
    in
    let tyevent = H.find decl_types Type.type_event in
    let se = if qv then AE.Symbols.var eid else AE.Symbols.name eid in
    let te = AE.Term.make se [] AE.Ty.Tint in
    let tem = AE.Term.make (AE.Symbols.name "e") [te] tyevent in
    let sav = AE.Symbols.Op (AE.Symbols.Access (AE.Hstring.make f)) in
    AE.Term.make sav [tem] ty

  let make_event_field ?(qv=false) e f =
    make_eventid_field ~qv (Event.name e) f

  let is_int = AE.Term.is_int

  let is_real = AE.Term.is_real

end

module Formula = struct

  type comparator = Eq | Neq | Le | Lt
  type combinator = And | Or | Imp | Not

  type literal = AE.Literal.LT.t
  
  type t = 
    | Lit of literal
    | Comb of combinator * t list

  let rec print fmt phi = 
    match phi with
      | Lit a -> AE.Literal.LT.print fmt a
      | Comb (Not, [f]) -> 
	  fprintf fmt "not (%a)" print f
      | Comb (And, l) -> fprintf fmt "(%a)" (print_list "and") l
      | Comb (Or, l) ->  fprintf fmt "(%a)" (print_list "or") l
      | Comb (Imp, [f1; f2]) -> 
	  fprintf fmt "%a => %a" print f1 print f2
      | _ -> assert false
  and print_list sep fmt = function
    | [] -> ()
    | [f] -> print fmt f
    | f::l -> fprintf fmt "%a %s %a" print f sep (print_list sep) l

  let f_true = Lit AE.Literal.LT.vrai
  let f_false = Lit AE.Literal.LT.faux
    
  let make_lit cmp l =
    let lit = 
      match cmp, l with
        | Eq, [t1; t2] ->
	    AE.Literal.LT.mkv_eq t1 t2
	| Neq, ts -> 
	  (*AE.Literal.LT.mkv_distinct false ts*)
	    AE.Literal.LT.mkv_builtin true (AE.Hstring.make "distinct") ts
	| Le, [t1; t2] ->
	    AE.Literal.LT.mkv_builtin true (AE.Hstring.make "<=") [t1; t2]
	| Lt, [t1; t2] ->
	    AE.Literal.LT.mkv_builtin true (AE.Hstring.make "<") [t1; t2]
	| _ -> assert false
    in
    Lit (AE.Literal.LT.make lit)

  let rec sform = function
    | Comb (Not, [Lit a]) -> Lit (AE.Literal.LT.neg a)
    | Comb (Not, [Comb (Not, [f])]) -> f
    | Comb (Not, [Comb (Or, l)]) ->
	let nl = List.map (fun a -> sform (Comb (Not, [a]))) l in
	Comb (And, nl)
    | Comb (Not, [Comb (And, l)]) ->  
	let nl = List.map (fun a -> sform (Comb (Not, [a]))) l in
	Comb (Or, nl)
    | Comb (Not, [Comb (Imp, [f1; f2])]) -> 
	Comb (And, [sform f1; sform (Comb (Not, [f2]))])
    | Comb (And, l) -> 
	Comb (And, List.map sform l)
    | Comb (Or, l) -> 
	Comb (Or, List.map sform l)
    | Comb (Imp, [f1; f2]) -> 
	Comb (Or, [sform (Comb (Not, [f1])); sform f2])
    | Comb (Imp, _) -> assert false
    | f -> f

  let make comb l = Comb (comb, l)

  let make_or = function
    | [] -> assert false
    | [a] -> a
    | l -> Comb (Or, l)

  let distrib l_and l_or = 
    let l = 
      if l_or = [] then l_and
      else
	List.map 
	  (fun x -> 
	     match x with 
	       | Lit _ -> Comb (Or, x::l_or)
	       | Comb (Or, l) -> Comb (Or, l@l_or)
	       | _ -> assert false
	  ) l_and 
    in
    Comb (And, l)

  let rec flatten_or = function
    | [] -> []
    | Comb (Or, l)::r -> l@(flatten_or r)
    | Lit a :: r -> (Lit a)::(flatten_or r)
    | _ -> assert false
    
  let rec flatten_and = function
    | [] -> []
    | Comb (And, l)::r -> l@(flatten_and r)
    | a :: r -> a::(flatten_and r)
    
  let rec cnf f = 
    match f with
      | Comb (Or, hd::tl) ->
	begin
	  let hd' = cnf hd in
	  let tl' = cnf (Comb (Or, tl)) in
	  match hd', tl' with
	    | hd', Comb (And, tl') ->
	      Comb (And, List.map (fun x -> cnf (Comb (Or, [hd'; x]))) tl')
	    | Comb (And, hd'), tl' ->
	      Comb (And, List.map (fun x -> cnf (Comb (Or, [x; tl']))) hd')
	    | _, _ -> f 
	end
      | Comb (And, l) -> 
	  Comb (And, List.map cnf l)
      | f -> f


let ( @@ ) l1 l2 = List.rev_append l1 l2

let rec mk_cnf = function
  | Comb (And, l) ->
      List.fold_left (fun acc f ->  (mk_cnf f) @@ acc) [] l

  | Comb (Or, [f1;f2]) ->
      let ll1 = mk_cnf f1 in
      let ll2 = mk_cnf f2 in
      List.fold_left 
	(fun acc l1 -> (List.rev_map (fun l2 -> l1 @@ l2)ll2) @@ acc) [] ll1

  | Comb (Or, f1 :: l) ->
      let ll1 = mk_cnf f1 in
      let ll2 = mk_cnf (Comb (Or, l)) in
      List.fold_left 
	(fun acc l1 -> (List.rev_map (fun l2 -> l1 @@ l2)ll2) @@ acc) [] ll1

  | Lit a -> [[a]]
  | Comb (Not, [Lit a]) -> [[AE.Literal.LT.neg a]]
  | _ -> assert false


  let rec unfold mono f = 
    match f with
      | Lit a -> a::mono 
      | Comb (Not, [Lit a]) -> 
	  (AE.Literal.LT.neg a)::mono
      | Comb (Or, l) -> 
	  List.fold_left unfold mono l
      | _ -> assert false
	  
  let rec init monos f = 
    match f with
      | Comb (And, l) -> 
	  List.fold_left init monos l
      | f -> (unfold [] f)::monos

  let make_cnf f =
    let sfnc = cnf (sform f) in
    init [] sfnc

  (* let make_cnf f = mk_cnf (sform f) *)

  let make_event_desc e =
    let tetid = Term.make_event_field e "tid" in
    let tedir = Term.make_event_field e "dir" in
    let teloc = Term.make_event_field e "loc" in    
    let stid = AE.Symbols.name (Hstring.view e.Event.tid) in
    let ttid = AE.Term.make stid [] AE.Ty.Tint in
    let dir = if e.Event.dir = Event.ERead then "_R" else "_W" in
    let tdir = Term.make_app (Hstring.make dir) [] in
    let loc = "_V" ^ (Hstring.view (fst e.Event.var)) in
    let tloc = Term.make_app (Hstring.make loc) [] in
    [ make_lit Eq [ tetid ; ttid ] ;
      make_lit Eq [ tedir ; tdir ] ;
      make_lit Eq [ teloc ; tloc ] ]

  let make_term_rel rel e1 e2 =
    let se1 = AE.Symbols.name e1 in
    let se2 = AE.Symbols.name e2 in
    let te1 = AE.Term.make se1 [] AE.Ty.Tint in
    let te2 = AE.Term.make se2 [] AE.Ty.Tint in
    AE.Term.make (AE.Symbols.name rel) [te1 ; te2] AE.Ty.Tbool

  let make_acyclic_rel e =
    let e = Event.name e in
    [ make_lit Eq [ make_term_rel "po_loc_U_com" e e ; Term.t_false ] ;
      make_lit Eq [ make_term_rel "co_U_prop" e e ; Term.t_false ] ]

  let make_pair rel (eid1, eid2) =
    let e1 = "e" ^ (string_of_int eid1) in
    let e2 = "e" ^ (string_of_int eid2) in
    make_lit Eq [ make_term_rel rel e1 e2 ; Term.t_true ]

  let make_rel rel pl =
    List.fold_left (fun f p -> make_pair rel p :: f) [] pl

  let make_cands rel cands =
    List.fold_left (fun ff pl ->
      Comb (Or, (make_rel rel pl)) :: ff
    ) [] cands

end

exception Unsat of int list

let set_cc b = Cc.cc_active := b
let set_arith = Combine.CX.set_arith_active
let set_sum = Combine.CX.set_sum_active

module type Solver = sig
  val check_strategy : check_strategy

  val get_time : unit -> float
  val get_calls : unit -> int

  val clear : unit -> unit
  val assume : ?events:Event.structure -> id:int -> Formula.t -> unit
  val check : ?fp:bool -> unit -> unit

  val entails : Formula.t -> bool
  val push : unit -> unit
  val pop : unit -> unit
end

module Make (Options : sig val profiling : bool end) = struct

  let check_strategy = Lazy

  let push_stack = Stack.create ()
  
  let calls = ref 0
  module Time = Timer.Make (Options)

  let get_time = Time.get
  let get_calls () = !calls

  module CSolver = Solver.Make (Options)

  (***********************************************)

  let clear () =
    all_events := [];
    formula := [](*;
    Stack.clear push_stack;
    CSolver.clear ()*)

(*let check_unsatcore uc =
    eprintf "Unsat Core : @.";
    List.iter 
      (fun c -> 
        eprintf "%a@." (Formula.print_list "or") 
          (List.map (fun x -> Formula.Lit x) c)) uc;
    eprintf "@.";
    try 
      clear ();
      CSolver.assume uc 0;
      CSolver.solve ();
      eprintf "Not an unsat core !!!@.";
      assert false
    with 
      | Solver.Unsat _ -> ();
      | Solver.Sat  -> 
          eprintf "Sat: Not an unsat core !!!@.";
          assert false

  let export_unsatcore cl = 
    let uc = List.map (fun {Solver_types.atoms=atoms} ->
      let l = ref [] in
      for i = 0 to Vec.size atoms - 1 do
        l := (Vec.get atoms i).Solver_types.lit :: !l
      done; 
      !l) cl
    in (* check_unsatcore uc; *)
    uc

  module SInt = 
    Set.Make (struct type t = int let compare = Pervasives.compare end)

  let export_unsatcore2 cl =
    let s = 
      List.fold_left 
        (fun s {Solver_types.name = n} ->
	  try SInt.add (int_of_string n) s with _ -> s) SInt.empty cl
    in 
    SInt.elements s *)
		 
  let assume ?(events=Event.empty_struct) ~id f =
    Time.start ();
    try
      if events <> Event.empty_struct then
	all_events := events :: !all_events;
      formula := (Formula.make_cnf f) :: !formula;
      (*CSolver.assume (Formula.make_cnf f) id;*)
      Time.pause ()
    with Solver.Unsat ex ->
      Time.pause ();
      raise (Unsat [] (*(export_unsatcore2 ex)*))

  let check ?(fp=false) () =
    incr calls;
    Time.start ();
    try

      let id =
	let c = ref 0 in
	fun () -> c := !c + 1; !c in

      let mk_true () =
	AE.Formula.mk_lit AE.Literal.LT.vrai (id ()) in

      let mk_eq t1 t2 =
	AE.Formula.mk_lit (AE.Literal.LT.mk_eq t1 t2) (id ()) in

      let mk_neq t1 t2 =
	AE.Formula.mk_not (mk_eq t1 t2) in

      let mk_eq_true t =
	mk_eq t Term.t_true in

      let mk_eq_false t =
	mk_eq t Term.t_false in

      let mk_and t1 t2 =
	AE.Formula.mk_and t1 t2 (id ()) in

      let mk_or t1 t2 =
	AE.Formula.mk_or t1 t2 (id ()) in

      let mk_imp t1 t2 =
	AE.Formula.mk_imp t1 t2 (id ()) in

      let rec mk_diff t1 = function
	| [] -> assert false
	| [t2] -> mk_neq t1 t2
	| t2 :: tl -> mk_and (mk_neq t1 t2) (mk_diff t1 tl)
      in

      let rec mk_all_diff = function
	| [] | [_] -> mk_true ()
	| t :: tl -> mk_and (mk_diff t tl) (mk_all_diff tl)
      in

      let mk_lit l = match (AE.Literal.LT.view l) with
        | AE.Literal.Builtin (true, n, ll) when AE.Hstring.view n = "distinct"
	    -> mk_all_diff ll
	| _ -> AE.Formula.mk_lit l (id ())
      in
	
      let rec mk_clause = function
	| [] -> mk_true ()
	| [l] -> mk_lit l
	| l :: ll -> mk_or (mk_lit l) (mk_clause ll)
      in

      let rec mk_cnf = function
	| [] -> mk_true ()
	| [c] -> mk_clause c
	| c :: cl -> mk_and (mk_clause c) (mk_cnf cl)
      in

      let rec mk_formula = function
	| [] -> mk_true ()
	| [c] -> mk_cnf c
	| c :: cl -> mk_and (mk_cnf c) (mk_formula cl)
      in

      let mk_forall n up bv tr f =
	let mk_vterm = List.map (fun (v, t) ->
	  AE.Term.make (AE.Symbols.name v) [] t) in (* OR VAR ?*)
	let up = mk_vterm up in
	let bv = mk_vterm bv in
	AE.Formula.mk_forall
	  (AE.Term.Set.of_list up) (* upvars = vars bound before *)
	  (AE.Term.Set.of_list bv) (* bvars = qtf vars in formula *)
	  tr f n (id ())
      in

      let mk_axiom n up bv tr f =
	let fa = mk_forall n up bv tr f in
	WPT.{ st_decl = Assume(fa, true) ; st_loc = dl }
      in

      let mk_pair ?(qv=false) rel e1 e2 =
	let se1 = if qv then AE.Symbols.var e1 else AE.Symbols.name e1 in
	let se2 = if qv then AE.Symbols.var e2 else AE.Symbols.name e2 in
	let te1 = AE.Term.make se1 [] AE.Ty.Tint in
	let te2 = AE.Term.make se2 [] AE.Ty.Tint in
        AE.Term.make (AE.Symbols.name rel) [te1 ; te2] AE.Ty.Tbool
      in

      let mk_dir d =
	let dir = if d = Event.ERead then "_R" else "_W" in
	Term.make_app (Hstring.make dir) [] in

      let mk_ety e = (e, AE.Ty.Tint) in

      let mk_evt_f ?(qv = false) e f =
	Term.make_eventid_field ~qv e f in

      (* Generate TSO axioms *)

      let qv = true in

      let axiom_rf = mk_axiom "axiom_rf" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "rf" "e1" "e2" ], None ]
	(mk_imp
	   (mk_eq_true (mk_pair ~qv "rf" "e1" "e2"))
	   (mk_eq (mk_evt_f ~qv "e1" "val") (mk_evt_f ~qv "e2" "val")))
      in

      let axiom_po_loc = mk_axiom "axiom_po_loc" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "po" "e1" "e2" ], None ]
	(mk_imp
	   (mk_and
	     (mk_eq_true (mk_pair ~qv "po" "e1" "e2"))
	     (mk_eq (mk_evt_f ~qv "e1" "loc") (mk_evt_f ~qv "e2" "loc")))
	   (mk_eq_true (mk_pair ~qv "po_loc_U_com" "e1" "e2")))
      in

      let axiom_rfe = mk_axiom "axiom_rfe" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "rf" "e1" "e2" ], None ]
	(mk_imp
	   (mk_and
	     (mk_eq_true (mk_pair ~qv "rf" "e1" "e2"))
	     (mk_neq (mk_evt_f ~qv "e1" "tid") (mk_evt_f ~qv "e2" "tid")))
	   (mk_eq_true (mk_pair ~qv "co_U_prop" "e1" "e2")))
      in

      let axiom_fr = mk_axiom "axiom_fr" []
        [ mk_ety "e1" ; mk_ety "e2" ; mk_ety "e3" ]
	[ [ mk_pair ~qv "rf" "e1" "e2" ; mk_pair ~qv "co" "e1" "e3" ], None ]
	(mk_imp
	   (mk_and
	     (mk_eq_true (mk_pair ~qv "rf" "e1" "e2"))
	     (mk_eq_true (mk_pair ~qv "co" "e1" "e3")))
	   (mk_and
	     (mk_eq_true (mk_pair ~qv "po_loc_U_com" "e2" "e3"))
	     (mk_eq_true (mk_pair ~qv "co_U_prop" "e2" "e3"))))
      in

      let axiom_ppo_tso = mk_axiom "axiom_ppo_tso" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "po" "e1" "e2" ], None ]
	(mk_imp
	   (mk_and
	     (mk_eq_true (mk_pair ~qv "po" "e1" "e2"))
	     (mk_or
	       (mk_neq (mk_evt_f ~qv "e1" "dir") (mk_dir Event.EWrite))
	       (mk_neq (mk_evt_f ~qv "e2" "dir") (mk_dir Event.ERead))))
	   (mk_eq_true (mk_pair ~qv "co_U_prop" "e1" "e2")))
      in

      let axiom_po_U_com_1 = mk_axiom "axiom_po_U_com_1" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "co" "e1" "e2" ], None (*;
	  [ mk_pair ~qv "po_loc_U_com" "e1" "e2" ], None*) ]
	(mk_imp
	  (mk_eq_true (mk_pair ~qv "co" "e1" "e2"))
	  (mk_eq_true (mk_pair ~qv "po_loc_U_com" "e1" "e2")))
      in

      let axiom_po_U_com_2 = mk_axiom "axiom_po_U_com_2" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "rf" "e1" "e2" ], None (*;
	  [ mk_pair ~qv "po_loc_U_com" "e1" "e2" ], None*) ]
	(mk_imp
	  (mk_eq_true (mk_pair ~qv "rf" "e1" "e2"))
	  (mk_eq_true (mk_pair ~qv "po_loc_U_com" "e1" "e2")))
      in

      let axiom_po_U_com_t = mk_axiom "axiom_po_U_com_t" []
        [ mk_ety "e1" ; mk_ety "e2" ; mk_ety "e3" ]
	[ [ mk_pair ~qv "po_loc_U_com" "e1" "e2" ;
	    mk_pair ~qv "po_loc_U_com" "e2" "e3" ], None ]
	(mk_imp
	   (mk_and
	     (mk_eq_true (mk_pair ~qv "po_loc_U_com" "e1" "e2"))
	     (mk_eq_true (mk_pair ~qv "po_loc_U_com" "e2" "e3")))
	   (mk_eq_true (mk_pair ~qv "po_loc_U_com" "e1" "e3")))
      in

      let axiom_co_U_prop_1 = mk_axiom "axiom_co_U_prop_1" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "co" "e1" "e2" ], None (*;
	  [ mk_pair ~qv "co_U_prop" "e1" "e2" ], None*) ]
	(mk_imp
	  (mk_eq_true (mk_pair ~qv "co" "e1" "e2"))
	  (mk_eq_true (mk_pair ~qv "co_U_prop" "e1" "e2")))
      in

      let axiom_co_U_prop_2 = mk_axiom "axiom_co_U_prop_2" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "fence" "e1" "e2" ], None (*;
	  [ mk_pair ~qv "co_U_prop" "e1" "e2" ], None*) ]
	(mk_imp
	  (mk_eq_true (mk_pair ~qv "fence" "e1" "e2"))
	  (mk_eq_true (mk_pair ~qv "co_U_prop" "e1" "e2")))
      in

      let axiom_co_U_prop_t = mk_axiom "axiom_co_U_prop_t" []
        [ mk_ety "e1" ; mk_ety "e2" ; mk_ety "e3" ]
	[ [ mk_pair ~qv "co_U_prop" "e1" "e2" ;
	    mk_pair ~qv "co_U_prop" "e2" "e3" ], None ]
	(mk_imp
	   (mk_and
	     (mk_eq_true (mk_pair ~qv "co_U_prop" "e1" "e2"))
	     (mk_eq_true (mk_pair ~qv "co_U_prop" "e2" "e3")))
	   (mk_eq_true (mk_pair ~qv "co_U_prop" "e1" "e3")))
      in
 
      (* Generate goal formula *)
      let f = (mk_formula (List.rev !formula)) in
      let goal = WPT.{ st_decl = Query("", f, [], Thm) ; st_loc = dl } in

      (* Build queue for solver *)
      let q = Queue.create () in
      if not fp then begin
	  Queue.push axiom_rf q;
	  Queue.push axiom_po_loc q;
	  Queue.push axiom_rfe q;
	  Queue.push axiom_fr q;
	  Queue.push axiom_ppo_tso q;
	  Queue.push axiom_po_U_com_1 q;
	  Queue.push axiom_po_U_com_2 q;
	  Queue.push axiom_po_U_com_t q;
	  Queue.push axiom_co_U_prop_1 q;
	  Queue.push axiom_co_U_prop_2 q;
	  Queue.push axiom_co_U_prop_t q
      end;
      Queue.push goal q;

      
      (* Call solver and check result *)
      let report d s steps = match s with
	| FE.Unsat dep -> raise (Solver.Unsat [])
	| FE.Inconsistent -> raise (Solver.Unsat [])
	| FE.Unknown t -> raise (Solver.Sat)
	| FE.Sat t -> raise (Solver.Sat)
      in
      ignore (Queue.fold (FE.process_decl report)
        (SAT.empty (), true, AE.Explanation.empty) q);

      (*CSolver.solve ();*)
      Time.pause ()
    with
      | Solver.Sat -> Time.pause ()
      | Solver.Unsat ex ->
	  Time.pause ();
	  raise (Unsat [] (*(export_unsatcore2 ex)*))

  (*let save_state = CSolver.save

  let restore_state = CSolver.restore*)

  let entails f = failwith "Alt_ergo.entails unsupported"
    (*let st = save_state () in
    let ans = 
      try
        assume ~id:0 (Formula.make Formula.Not [f]) ;
        check ();
        false
      with Unsat _ -> true
    in
    restore_state st;
    ans*)

  let push () = (*Stack.push (save_state ()) push_stack*)
    failwith "Alt_ergo.push unsupported"

  let pop () = (*Stack.pop push_stack |> restore_state*)
    failwith "Alt_ergo.pop unsupported"

end







(*
      let axiom_rf = mk_axiom 0 "axiom_rf" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "rf" "e1" "e2" ], None ]
	(mk_imp 0
	   (mk_eq_true 0 (mk_pair ~qv "rf" "e1" "e2"))
	   (mk_eq 0 (mk_evt_f ~qv "e1" "val") (mk_evt_f ~qv "e2" "val")))
      in

      let axiom_po_loc = mk_axiom 0 "axiom_po_loc" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "po" "e1" "e2" ], None ]
	(mk_imp 0
	   (mk_and 0
	     (mk_eq_true 0 (mk_pair ~qv "po" "e1" "e2"))
	     (mk_eq 0 (mk_evt_f ~qv "e1" "loc") (mk_evt_f ~qv "e2" "loc")))
	   (mk_eq_true 0 (mk_pair ~qv "po_loc" "e1" "e2")))
      in

      let axiom_rfe = mk_axiom 0 "axiom_rfe" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "rf" "e1" "e2" ], None ]
	(mk_imp 0
	   (mk_and 0
	     (mk_eq_true 0 (mk_pair ~qv "rf" "e1" "e2"))
	     (mk_neq 0 (mk_evt_f ~qv "e1" "tid") (mk_evt_f ~qv "e2" "tid")))
	   (mk_eq_true 0 (mk_pair ~qv "rfe" "e1" "e2")))
      in

      let axiom_fr = mk_axiom 0 "axiom_fr" []
        [ mk_ety "e1" ; mk_ety "e2" ; mk_ety "e3" ]
	[ [ mk_pair ~qv "rf" "e1" "e2" ; mk_pair ~qv "co" "e1" "e3" ], None ]
	(mk_imp 0
	   (mk_and 0
	     (mk_eq_true 0 (mk_pair ~qv "rf" "e1" "e2"))
	     (mk_eq_true 0 (mk_pair ~qv "co" "e1" "e3")))
	   (mk_eq_true 0 (mk_pair ~qv "fr" "e2" "e3")))
      in

      let axiom_ppo_tso = mk_axiom 0 "axiom_ppo_tso" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "po" "e1" "e2" ], None ]
	(mk_imp 0
	   (mk_and 0
	     (mk_eq_true 0 (mk_pair ~qv "po" "e1" "e2"))
	     (mk_or 0
	       (mk_neq 0 (mk_evt_f ~qv "e1" "dir") (mk_dir Event.EWrite))
	       (mk_neq 0 (mk_evt_f ~qv "e2" "dir") (mk_dir Event.ERead))))
	   (mk_eq_true 0 (mk_pair ~qv "ppo" "e1" "e2")))
      in

      let axiom_po_U_com = mk_axiom 0 "axiom_po_U_com" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "po_loc" "e1" "e2" ], None ;
	  [ mk_pair ~qv "co" "e1" "e2" ], None ;
	  [ mk_pair ~qv "rf" "e1" "e2" ], None ;
	  [ mk_pair ~qv "fr" "e1" "e2" ], None ]
	(mk_imp 0
	   (mk_or 0
	     (mk_eq_true 0 (mk_pair ~qv "po_loc" "e1" "e2"))
	     (mk_or 0
	       (mk_eq_true 0 (mk_pair ~qv "co" "e1" "e2"))
	       (mk_or 0
	         (mk_eq_true 0 (mk_pair ~qv "rf" "e1" "e2"))
	         (mk_eq_true 0 (mk_pair ~qv "fr" "e1" "e2")))))
	   (mk_eq_true 0 (mk_pair ~qv "po_loc_U_com" "e1" "e2")))
      in

      let axiom_po_U_com_t = mk_axiom 0 "axiom_po_U_com_t" []
        [ mk_ety "e1" ; mk_ety "e2" ; mk_ety "e3" ]
	[ [ mk_pair ~qv "po_loc_U_com" "e1" "e2" ;
	    mk_pair ~qv "po_loc_U_com" "e2" "e3" ], None ]
	(mk_imp 0
	   (mk_and 0
	     (mk_eq_true 0 (mk_pair ~qv "po_loc_U_com" "e1" "e2"))
	     (mk_eq_true 0 (mk_pair ~qv "po_loc_U_com" "e2" "e3")))
	   (mk_eq_true 0 (mk_pair ~qv "po_loc_U_com" "e1" "e3")))
      in

      let axiom_co_U_prop = mk_axiom 0 "axiom_co_U_prop" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "co" "e1" "e2" ], None ;
	  [ mk_pair ~qv "ppo" "e1" "e2" ], None ;
	  [ mk_pair ~qv "fence" "e1" "e2" ], None ;
	  [ mk_pair ~qv "rfe" "e1" "e2" ], None ;
	  [ mk_pair ~qv "fr" "e1" "e2" ], None ]
	(mk_imp 0
	   (mk_or 0
	     (mk_eq_true 0 (mk_pair ~qv "co" "e1" "e2"))
	     (mk_or 0
	       (mk_eq_true 0 (mk_pair ~qv "ppo" "e1" "e2"))
	       (mk_or 0
	         (mk_eq_true 0 (mk_pair ~qv "fence" "e1" "e2"))
	         (mk_or 0
	           (mk_eq_true 0 (mk_pair ~qv "rfe" "e1" "e2"))
	           (mk_eq_true 0 (mk_pair ~qv "fr" "e1" "e2"))))))
	   (mk_eq_true 0 (mk_pair ~qv "co_U_prop" "e1" "e2")))
      in

      let axiom_co_U_prop_t = mk_axiom 0 "axiom_co_U_prop_t" []
        [ mk_ety "e1" ; mk_ety "e2" ; mk_ety "e3" ]
	[ [ mk_pair ~qv "co_U_prop" "e1" "e2" ;
	    mk_pair ~qv "co_U_prop" "e2" "e3" ], None ]
	(mk_imp 0
	   (mk_and 0
	     (mk_eq_true 0 (mk_pair ~qv "co_U_prop" "e1" "e2"))
	     (mk_eq_true 0 (mk_pair ~qv "co_U_prop" "e2" "e3")))
	   (mk_eq_true 0 (mk_pair ~qv "co_U_prop" "e1" "e3")))
      in
 *)



(*
      let make_event_desc e =
	let tetid = Term.make_event_field e "tid" in
	let tedir = Term.make_event_field e "dir" in
	let teloc = Term.make_event_field e "loc" in    
	let stid = AE.Symbols.name (Hstring.view e.Event.tid) in
	let ttid = AE.Term.make stid [] AE.Ty.Tint in
	let dir = if e.Event.dir = Event.ERead then "_R" else "_W" in
	let tdir = Term.make_app (Hstring.make dir) [] in
	let loc = "_V" ^ (Hstring.view (fst e.Event.var)) in
	let tloc = Term.make_app (Hstring.make loc) [] in
	(mk_and 10
	  (mk_eq 11 tetid ttid)
	  (mk_and 12
	    (mk_eq 13 tedir tdir)
	    (mk_eq 14 teloc tloc))) in

      AE.Options.set_verbose true;
      let qv = true in

      let axiom_rf = mk_axiom 0 "axiom_rf" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "rf" "e1" "e2" ], None ]
	(mk_imp 1
	   (mk_eq_true 2 (mk_pair ~qv "rf" "e1" "e2"))
	   (mk_eq 3 (mk_evt_f ~qv "e1" "loc") (mk_evt_f ~qv "e2" "loc")))
      in

      let e1 =  Event.{ uid = 4; tid = Hstring.make "#1";
			dir = Event.EWrite; var = Hstring.make "X", [] } in
      let e2 =  Event.{ uid = 5; tid = Hstring.make "#1";
			dir = Event.ERead; var = Hstring.make "X", [] } in
      let e1d = make_event_desc e1 in
      let e2d = make_event_desc e2 in

      let f = (mk_imp 4
	        (mk_and 5
	          (mk_and 6 e1d e2d)
		  (mk_eq_true 7 (mk_pair "rf" "e4" "e5")))
		(mk_eq 8 (mk_evt_f "e4" "loc") (mk_evt_f "e5" "loc"))) in
      let goal = WPT.{ st_decl = Query("g", f, [], Thm) ; st_loc = dl } in

      let q = Queue.create () in
      Queue.push axiom_rf q;
      Queue.push goal q;
 *)
(*


      let axiom_rf = mk_axiom 1 "axiom_rf" []
        [ mk_ety "e1" ; mk_ety "e2" ]
	[ [ mk_pair ~qv "rf" "e1" "e2" ], None ]
	(mk_imp 2
	   (mk_eq_true 3 (mk_pair ~qv "rf" "e1" "e2"))
	   (mk_eq_true 4 (mk_pair ~qv "rfe" "e1" "e2"))) in

      let f = (mk_and 5
	        (mk_eq_true 6 (mk_pair "rf" "e4" "e5"))
		(mk_eq_false 7 (mk_pair "rfe" "e4" "e5"))) in
      let goal = WPT.{ st_decl = Query("g", f, [], Thm) ; st_loc = dl } in

      let q = Queue.create () in
      Queue.push axiom_rf q;
      Queue.push goal q;
 *)
      
(*
      let x = AE.Term.make (AE.Symbols.var "x") [] AE.Ty.Tint in
      let fx = AE.Term.make (AE.Symbols.name "f") [x] AE.Ty.Tint in
      let n42 = AE.Term.int "42" in
      let n43 = AE.Term.int "43" in
      let fn42 = AE.Term.make (AE.Symbols.name "f") [n42] AE.Ty.Tint in
      let fn43 = AE.Term.make (AE.Symbols.name "f") [n43] AE.Ty.Tint in

      let axiom_x = mk_axiom 1 "axiom_x" [ ]
	[ mk_ety "x" ]
	[ [ fx ], None ]
	(AE.Formula.mk_lit (AE.Literal.LT.mk_eq fx x) 2) in
      let f = match axiom_x.WPT.st_decl with Assume(fa, b) -> fa in
      AE.Formula.print std_formatter f;
      Format.fprintf std_formatter "\n";

      let l = AE.Literal.LT.mk_eq fn42 n43 in
      let f = AE.Formula.mk_lit (l) 3 in
      AE.Formula.print std_formatter f;
      Format.fprintf std_formatter "\n";
      let goal = WPT.{ st_decl = Query("g", f, [], Thm) ; st_loc = dl } in

      let q = Queue.create () in
      Queue.push axiom_x q;
      Queue.push goal q;
 *)
