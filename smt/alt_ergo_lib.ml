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

let hsca chs = AE.Hstring.make (Hstring.view chs)
let hsac ahs = Hstring.make (AE.Hstring.view ahs)
let lhsca lchs = List.map hsca lchs
let lhsac lahs = List.map hsac lahs
       
type error = 
  | DuplicateTypeName of Hstring.t
  | DuplicateSymb of Hstring.t
  | UnknownType of Hstring.t
  | UnknownSymb of Hstring.t

exception Error of error

let report fmt = function
  | DuplicateTypeName s ->
      fprintf fmt "duplicate type name for %a" Hstring.print s
  | DuplicateSymb e ->
      fprintf fmt "duplicate name for %a" Hstring.print e
  | UnknownType s ->
      fprintf fmt "unknown type %a" Hstring.print s
  | UnknownSymb s ->
      fprintf fmt "unknown symbol %a" Hstring.print s

type check_strategy = Lazy | Eager
                      
module H = Hstring.H
module HSet = Hstring.HSet

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

  let type_prop = 
    let tprop = Hstring.make "prop" in
    H.add decl_types tprop AE.Ty.Tbool;
    tprop

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

  let declare_field ty f =
    if H.mem decl_symbs f then raise (Error (DuplicateSymb f));
    H.add decl_symbs f (AE.Symbols.Op (AE.Symbols.Access (hsca f)), [], ty)

  let declare_record t fields =
    if H.mem decl_types t then raise (Error (DuplicateTypeName t));
    let tfields = List.map (fun (f, ty) -> (hsca f, H.find decl_types ty)) fields in
    let ty = AE.Ty.Trecord AE.Ty.{ args = []; name = hsca t; lbs = tfields } in
    H.add decl_types t ty;
    List.iter (fun (f, ty) -> declare_field ty f) fields

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

end

module Symbol = struct
    
  type t = Hstring.t

  let declare f args ret =
    if H.mem decl_symbs f then raise (Error (DuplicateTypeName f));
    List.iter 
      (fun t -> 
	if not (H.mem decl_types t) then raise (Error (UnknownType t)) )
      (ret::args);
    H.add decl_symbs f (AE.Symbols.name (Hstring.view f), args, ret)

  let type_of s = let _, args, ret = H.find decl_symbs s in args, ret

  let is_weak s =
    try snd (type_of (Hstring.make ("_V" ^ Hstring.view s))) =
	  (Hstring.make "_weak_var")
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
	   (* begin match ts with *)
	   (*   | t1 :: t2 :: [] -> *)
		AE.Literal.LT.mkv_distinct false ts
	     	(* AE.Literal.LT.view (AE.Literal.LT.neg *)
	     	(* 		      (AE.Literal.LT.mk_eq t1 t2)) *)
	   (*   | _ -> AE.Literal.LT.mkv_builtin false *)
	   (*   			   (AE.Hstring.make "distinct") ts *)
	   (* end *)
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

end

(* module WPT = AE.Why_ptree *)
module WPT = AE.Commands
module SAT = (val (AE.Sat_solvers.get_current ()) : AE.Sat_solvers.S)
module FE = AE.Frontend.Make(SAT)

exception Unsat of int list

let set_cc b = Cc.cc_active := b
let set_arith = Combine.CX.set_arith_active
let set_sum = Combine.CX.set_sum_active

module type Solver = sig
  val init_axioms : unit -> unit
    
  val check_strategy : check_strategy

  val get_time : unit -> float
  val get_calls : unit -> int

  val clear : unit -> unit
  val assume : id:int -> Formula.t -> unit
  val check : ?fp:bool -> unit -> unit

  val entails : Formula.t -> bool
  val push : unit -> unit
  val pop : unit -> unit
end

module Make (Options_ : sig val profiling : bool end) = struct

  (********** weak memory stuff **********)

  let axioms = Queue.create ()

  let mk_symb ?(qv=false) s =
    if qv then AE.Symbols.var s else AE.Symbols.name s

  let mk_pred ?(qv=false) p al =
    let al = List.map (fun a ->
      AE.Term.make (mk_symb ~qv a) [] AE.Ty.Tint) al in
    AE.Term.make (AE.Symbols.name p) al AE.Ty.Tbool

  let mk_fun ?(qv=false) p al =
    let al = [ fst al ; snd al ] in
    let al = List.map (fun a ->
      AE.Term.make (mk_symb ~qv a) [] AE.Ty.Tint) al in
    AE.Term.make (AE.Symbols.name p) al AE.Ty.Tint

  let mk_evt_f ?(qv=false) (p, e, s) f =
    let tp = AE.Term.make (mk_symb ~qv p) [] AE.Ty.Tint in
    let te = AE.Term.make (mk_symb ~qv e) [] AE.Ty.Tint in
    let ts = AE.Term.make (mk_symb ~qv s) [] AE.Ty.Tint in
    let tem = Term.make_app (Hstring.make "_e") [tp;te;ts] in
    Term.make_app (Hstring.make f) [tem]

  let dl = (Lexing.dummy_pos, Lexing.dummy_pos)
  let id = let c = ref 0 in fun () -> c := !c + 1; !c
  let mk_lt t1 t2 =
    AE.Formula.mk_lit
      (AE.Literal.LT.mk_builtin true (AE.Hstring.make "<") [t1;t2]) (id ())
  let mk_ety e = (e, AE.Ty.Tint)
  let mk_true () = AE.Formula.mk_lit AE.Literal.LT.vrai (id ())
  let mk_eq t1 t2 = AE.Formula.mk_lit (AE.Literal.LT.mk_eq t1 t2) (id ())
  let mk_neq t1 t2 = AE.Formula.mk_not (mk_eq t1 t2)
  let mk_eq_true t = mk_eq t Term.t_true
  let mk_eq_false t = mk_eq t Term.t_false
  let mk_and t1 t2 = AE.Formula.mk_and t1 t2 false (id ()) (* new param : is_impl -> false *)
  let mk_or t1 t2 = AE.Formula.mk_or t1 t2 false (id ())  (* new param : is_impl -> false *)
  let mk_imp t1 t2 = AE.Formula.mk_imp t1 t2 (id ())
  let rec mk_diff t1 = function
    | [] -> assert false
    | [t2] -> mk_neq t1 t2
    | t2 :: tl -> mk_and (mk_neq t1 t2) (mk_diff t1 tl)
  let rec mk_all_diff = function
    | [] | [_] -> mk_true ()
    | t :: tl -> mk_and (mk_diff t tl) (mk_all_diff tl)
  let mk_lit l = match (AE.Literal.LT.view l) with
    | AE.Literal.Builtin (true, n, ll) when AE.Hstring.view n = "distinct"
      -> mk_all_diff ll
    | AE.Literal.Distinct (false, ll)
      -> mk_all_diff ll
    | _ -> AE.Formula.mk_lit l (id ())
  let rec mk_clause = function
    | [] -> mk_true ()
    | [l] -> mk_lit l
    | l :: ll -> mk_or (mk_lit l) (mk_clause ll)
  let rec mk_cnf = function
    | [] -> mk_true ()
    | [c] -> mk_clause c
    | c :: cl -> mk_and (mk_clause c) (mk_cnf cl)
  (* let rec mk_formula = function *)
  (*   | [] -> mk_true () *)
  (*   | [c] -> mk_cnf c *)
  (*   | c :: cl -> mk_and (mk_cnf c) (mk_formula cl) *)
  let rec mk_formula = function
    | [] -> mk_true ()
    | [c] -> mk_cnf c
    | cl -> mk_cnf (List.flatten cl)
  (* let mk_forall n up bv tr f = *)
  (*   let mk_vterm = List.map (fun (v, t) -> *)
  (*     AE.Term.make (AE.Symbols.var v) [] t) in *)
  (*   let up = mk_vterm up in (\* should be empty *\) *)
  (*   let bv = mk_vterm bv in *)
  (*   AE.Formula.mk_forall *)
  (*     (AE.Term.Set.of_list up) (\* upvars = vars bound before *\) *)
  (*     (AE.Term.Set.of_list bv) (\* bvars = qtf vars in formula *\) *)
  (*     tr f n (id ()) *)
  let mk_forall n up bv tr f =
    let mk_vterm = List.map (fun (v, t) ->
      AE.Term.make (AE.Symbols.var v) [] t) in
    let qvars = AE.Term.Set.of_list (mk_vterm bv) in (* bvars = qtf vars in f *)
    let binders = AE.Formula.mk_binders qvars in
    AE.Formula.mk_forall n dl binders tr f (id ()) None
  let mk_axiom n up bv tr f =
    let f = mk_forall n up bv tr f in
    WPT.{ st_decl = Assume(f, true) ; st_loc = dl }
  let mk_goal f =
    let f = mk_formula f in
    WPT.{ st_decl = Query("g", f, [], (*Check*)AE.Typed.Thm) ; st_loc = dl }

  let init_axioms () =
    let qv = true in
    let ety2 = [ mk_ety "p1" ; mk_ety "p2" ; mk_ety "_e1" ; mk_ety "_e2" ] in
    let ety2s = [ mk_ety "p1" ; mk_ety "p2" ;
		  mk_ety "_e1" ; mk_ety "_e2" ;
		  mk_ety "_s1" ; mk_ety "_s2" ] in
    let ety3 = [ mk_ety "p1" ; mk_ety "p2" ; mk_ety "p3" ;
		 mk_ety "_e1" ; mk_ety "_e2" ; mk_ety "_e3" ] in
    let ety3s = [ mk_ety "p1" ; mk_ety "p2" ; mk_ety "p3" ;
		  mk_ety "_e1" ; mk_ety "_e2" ; mk_ety "_e3" ;
		  mk_ety "_s1" ; mk_ety "_s2" ; mk_ety "_s3" ] in
    let e1e2 = ["p1";"_e1";"p2";"_e2"] in
    let e1e2s = ["p1";"_e1";"_s1";"p2";"_e2";"_s2"] in
    let e2e3 = ["p2";"_e2";"p3";"_e3"] in
    let e2e3s = ["p2";"_e2";"_s2";"p3";"_e3";"_s3"] in
    let e1e3 = ["p1";"_e1";"p3";"_e3"] in
    let e1e3s = ["p1";"_e1";"_s1";"p3";"_e3";"_s3"] in
    let e1 = ("p1", "_e1") in
    let e2 = ("p2", "_e2") in
    let e3 = ("p3", "_e3") in
    let e1s = ("p1", "_e1", "_s1") in
    let e2s = ("p2", "_e2", "_s2") in
    let e3s = ("p3", "_e3", "_s3") in
    let tp1 = AE.Term.make (mk_symb ~qv "p1") [] AE.Ty.Tint in
    let tp2 = AE.Term.make (mk_symb ~qv "p2") [] AE.Ty.Tint in
    let tw = Term.make_app (Hstring.make "_W") [] in
    let tr = Term.make_app (Hstring.make "_R") [] in

(*    let axiom_rf_val = mk_axiom "axiom_rf_val" [] ety2s
      (* [ [ mk_pred ~qv "_rf" e1e2s ], None ] *)
      [ AE.Formula.{ content = [ mk_pred ~qv "_rf" e1e2s ]; depth = 0; from_user = true; guard = None } ]
      (mk_imp
    	(mk_eq_true (mk_pred ~qv "_rf" e1e2s))
    	(mk_eq (mk_evt_f ~qv e1s "_val") (mk_evt_f ~qv e2s "_val"))) in
    Queue.push axiom_rf_val axioms;*)

    let axiom_po_loc = mk_axiom "axiom_po_loc" [] ety2s
      (* [ [ mk_pred ~qv "_po_loc" e1e2s ], None ] *)
      [ AE.Formula.{ content = [ mk_pred ~qv "_po_loc" e1e2s ]; depth = 0; from_user = true; guard = None } ]
      (mk_imp
	(mk_eq_true (mk_pred ~qv "_po_loc" e1e2s))
	(mk_lt (mk_fun ~qv "_sci" e1) (mk_fun ~qv "_sci" e2))) in
    Queue.push axiom_po_loc axioms;

    let axiom_co_1 = mk_axiom "axiom_co_1" [] ety2s
      (* [ [ mk_pred ~qv "_co" e1e2s ], None ] *)
      [ AE.Formula.{ content = [ mk_pred ~qv "_co" e1e2s ]; depth = 0; from_user = true; guard = None } ]
      (mk_imp
    	(mk_eq_true (mk_pred ~qv "_co" e1e2s))
    	(mk_lt (mk_fun ~qv "_sci" e1) (mk_fun ~qv "_sci" e2))) in
    Queue.push axiom_co_1 axioms;

    let axiom_rf = mk_axiom "axiom_rf" [] ety2s
      (* [ [ mk_pred ~qv "_rf" e1e2s ], None ] *)
      [ AE.Formula.{ content = [ mk_pred ~qv "_rf" e1e2s ]; depth = 0; from_user = true; guard = None } ]
      (mk_imp
	(mk_eq_true (mk_pred ~qv "_rf" e1e2s))
	(mk_lt (mk_fun ~qv "_sci" e1) (mk_fun ~qv "_sci" e2))) in
    Queue.push axiom_rf axioms;

    let axiom_ppo = mk_axiom "axiom_ppo" [] ety2s
      (* [ [ mk_pred ~qv "_ppo" e1e2s ], None ] *)
      [ AE.Formula.{ content = [ mk_pred ~qv "_ppo" e1e2s ]; depth = 0; from_user = true; guard = None } ]
      (mk_imp
	(mk_eq_true (mk_pred ~qv "_ppo" e1e2s))
	(mk_lt (mk_fun ~qv "_propi" e1) (mk_fun ~qv "_propi" e2))) in
    Queue.push axiom_ppo axioms;

    let axiom_fence = mk_axiom "axiom_fence" [] ety2
      (* [ [ mk_pred ~qv "_fence" e1e2 ], None ] *)
      [ AE.Formula.{ content = [ mk_pred ~qv "_fence" e1e2 ]; depth = 0; from_user = true; guard = None } ]
      (mk_imp
    	(mk_eq_true (mk_pred ~qv "_fence" e1e2))
	(mk_lt (mk_fun ~qv "_propi" e1) (mk_fun ~qv "_propi" e2))) in
    Queue.push axiom_fence axioms;

    let axiom_co_2 = mk_axiom "axiom_co_2" [] ety2s
      (* [ [ mk_pred ~qv "_co" e1e2s ], None ] *)
      [ AE.Formula.{ content = [ mk_pred ~qv "_co" e1e2s ]; depth = 0; from_user = true; guard = None } ]
      (mk_imp
    	(mk_eq_true (mk_pred ~qv "_co" e1e2s))
    	(mk_lt (mk_fun ~qv "_propi" e1) (mk_fun ~qv "_propi" e2))) in
    Queue.push axiom_co_2 axioms;

    let axiom_rfe = mk_axiom "axiom_rfe" [] ety2s
      (* [ [ mk_pred ~qv "_rf" e1e2s ], None ] *)
      [ AE.Formula.{ content = [ mk_pred ~qv "_rf" e1e2s ]; depth = 0; from_user = true; guard = None } ]
      (mk_imp
    	(mk_and
    	  (mk_eq_true (mk_pred ~qv "_rf" e1e2s))
    	  (mk_neq tp1 tp2))
    	(mk_lt (mk_fun ~qv "_propi" e1) (mk_fun ~qv "_propi" e2))) in
    Queue.push axiom_rfe axioms;

    let axiom_fr = mk_axiom "axiom_fr" [] ety3s
      (* [ [ mk_pred ~qv "_rf" e1e2s ; mk_pred ~qv "_co" e1e3s ], None ] *)
      [ AE.Formula.{ content = [ mk_pred ~qv "_rf" e1e2s ; mk_pred ~qv "_co" e1e3s ]; depth = 0; from_user = true; guard = None } ]
      (mk_imp
    	(mk_and
    	  (mk_eq_true (mk_pred ~qv "_rf" e1e2s))
    	  (mk_eq_true (mk_pred ~qv "_co" e1e3s)))
    	(mk_and
    	  (mk_lt (mk_fun ~qv "_sci" e2) (mk_fun ~qv "_sci" e3))
    	  (mk_lt (mk_fun ~qv "_propi" e2) (mk_fun ~qv "_propi" e3)))) in
    Queue.push axiom_fr axioms

  let init_axioms () =
    if Options.model = Options.SC then ()
    else init_axioms ()

  let formula = ref []

  (***********************************************)

  let check_strategy = Lazy

  let push_stack = Stack.create ()
  
  let calls = ref 0
  module Time = Timer.Make (Options_)

  let get_time = Time.get
  let get_calls () = !calls

  (*module CSolver = Solver.Make (Options_)*)

  (***********************************************)

  let clear () =
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
		 
  let assume ~id f =
    Time.start ();
    try
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

      (* Initial queue *)
      let q = if fp then Queue.create () else Queue.copy axioms in

      (* Generate goal formula *)
      let goal = mk_goal (List.rev !formula) in
      Queue.push goal q;
      
      (* Call solver and check result *)
      let report d s steps = match s with
	| FE.Unsat dep -> raise (Solver.Unsat [])
	| FE.Inconsistent -> raise (Solver.Unsat [])
	| FE.Unknown t -> raise (Solver.Sat)
	| FE.Sat t -> raise (Solver.Sat)
      in
      (* SAT.start (); *)
      SAT.reset_refs (); (* was reset_steps *)
      ignore (Queue.fold (FE.process_decl report)
        (SAT.empty (), true, AE.Explanation.empty) q);

      (*CSolver.solve ();*)
      Time.pause ()
    with
      | Solver.Sat -> Time.pause ()
      | Solver.Unsat ex ->
	  Time.pause ();
	  raise (Unsat [] (*(export_unsatcore2 ex)*))

  (* let save_state = CSolver.save *)

  (* let restore_state = CSolver.restore *)

  let entails f =
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
    failwith "Alt_ergo_lib.entails unsupported"

  let push () = (*Stack.push (save_state ()) push_stack*)
    failwith "Alt_ergo_lib.push unsupported"

  let pop () = (*Stack.pop push_stack |> restore_state*)
    failwith "Alt_ergo_lib.pop unsupported"

end




(*
    let axiom_rf = mk_axiom "axiom_rf" [] ety2
      [ [ mk_pred ~qv "_rf" e1e2 ], None ]
      (mk_imp
    	(mk_eq_true (mk_pred ~qv "_rf" e1e2))
    	(mk_eq (mk_evt_f ~qv e1 "_val") (mk_evt_f ~qv e2 "_val"))) in
    Queue.push axiom_rf axioms;

    (* let axiom_po_loc = mk_axiom "axiom_po_loc" [] ety2 *)
    (*   [ [ mk_pred ~qv "_po" e1e2 ], None ] *)
    (*   (mk_imp *)
    (* 	(mk_and *)
    (* 	  (mk_eq_true (mk_pred ~qv "_po" e1e2)) *)
    (* 	  (mk_eq (mk_evt_f ~qv e1 "_var") (mk_evt_f ~qv e2 "_var"))) *)
    (* 	(mk_eq_true (mk_pred ~qv "_po_loc_U_com" e1e2))) in *)
    (* Queue.push axiom_po_loc axioms; *)

    let axiom_rfe = mk_axiom "axiom_rfe" [] ety2
      [ [ mk_pred ~qv "_rf" e1e2 ], None ]
      (mk_imp
    	(mk_and
    	  (mk_eq_true (mk_pred ~qv "_rf" e1e2))
    	  (mk_neq tp1 tp2))
    	(mk_lt (mk_fun ~qv "_propi" e1) (mk_fun ~qv "_propi" e2))) in
    	(* (mk_eq_true (mk_pred ~qv "_co_U_prop" e1e2))) in *)
    Queue.push axiom_rfe axioms;

    let axiom_fr = mk_axiom "axiom_fr" [] ety3
      [ [ mk_pred ~qv "_rf" e1e2 ; mk_pred ~qv "_co" e1e3 ], None ]
      (mk_imp
	(mk_and
	  (mk_eq_true (mk_pred ~qv "_rf" e1e2))
	  (mk_eq_true (mk_pred ~qv "_co" e1e3)))
	(mk_and
	  (mk_lt (mk_fun ~qv "_sci" e2) (mk_fun ~qv "_sci" e3))
	  (mk_lt (mk_fun ~qv "_propi" e2) (mk_fun ~qv "_propi" e3)))) in
	  (* (mk_eq_true (mk_pred ~qv "_po_loc_U_com" e2e3)) *)
	  (* (mk_eq_true (mk_pred ~qv "_co_U_prop" e2e3)))) in *)
    Queue.push axiom_fr axioms;

    (* Forall ([p1; e1; p2; e2; p3; e3], AE.Ty.Tint, *)
    (*  [[ Pred ("_rf", [p1; e1; p2; e2]); Pred ("_co", [p1; e1; p3; e3]) ]], *)
    (*  Imp (And (Eq (Pred ("_rf", [p1; e1; p2; e2]), True), *)
    (* 	       Eq (Pred ("_co", [p1; e1; p3; e3]), True)), *)
    (*       And (Eq (Pred ("_po_loc_U_com", [p2; e2; p3; e3]), True), *)
    (* 	       Eq (Pred ("_co_U_prop", [p2; e2; p3; e3]), True))) *)

    (* let axiom_ppo_tso = mk_axiom "axiom_ppo_tso" [] ety2 *)
    (*   [ [ mk_pred ~qv "_po" e1e2 ], None ] *)
    (*   (mk_imp *)
    (* 	(mk_and *)
    (* 	  (mk_eq_true (mk_pred ~qv "_po" e1e2)) *)
    (* 	  (mk_or *)
    (* 	    (mk_neq (mk_evt_f ~qv e1 "_dir") tw) *)
    (* 	    (mk_neq (mk_evt_f ~qv e2 "_dir") tr))) *)
    (* 	(mk_eq_true (mk_pred ~qv "_co_U_prop" e1e2))) in *)
    (* Queue.push axiom_ppo_tso axioms; *)

    let axiom_po_U_com_1 = mk_axiom "axiom_po_U_com_1" [] ety2
      [ [ mk_pred ~qv "_co" e1e2 ], None ]
      (mk_imp
	(mk_eq_true (mk_pred ~qv "_co" e1e2))
	(mk_lt (mk_fun ~qv "_sci" e1) (mk_fun ~qv "_sci" e2))) in
	(* (mk_eq_true (mk_pred ~qv "_po_loc_U_com" e1e2))) in *)
    Queue.push axiom_po_U_com_1 axioms;

    let axiom_po_U_com_2 = mk_axiom "axiom_po_U_com_2" [] ety2
      [ [ mk_pred ~qv "_rf" e1e2 ], None ]
      (mk_imp
	(mk_eq_true (mk_pred ~qv "_rf" e1e2))
	(mk_lt (mk_fun ~qv "_propi" e1) (mk_fun ~qv "_propi" e2))) in
	(* (mk_eq_true (mk_pred ~qv "_po_loc_U_com" e1e2))) in *)
    Queue.push axiom_po_U_com_2 axioms;

    (* let axiom_po_U_com_t = mk_axiom "axiom_po_U_com_t" [] ety3 *)
    (*   [ [ mk_pred ~qv "_po_loc_U_com" e1e2 ; *)
    (* 	  mk_pred ~qv "_po_loc_U_com" e2e3 ], None ] *)
    (*   (mk_imp *)
    (* 	(mk_and *)
    (* 	  (mk_eq_true (mk_pred ~qv "_po_loc_U_com" e1e2)) *)
    (* 	  (mk_eq_true (mk_pred ~qv "_po_loc_U_com" e2e3))) *)
    (* 	(mk_eq_true (mk_pred ~qv "_po_loc_U_com" e1e3))) in *)
    (* Queue.push axiom_po_U_com_t axioms; *)

    let axiom_co_U_prop_1 = mk_axiom "axiom_co_U_prop_1" [] ety2
      [ [ mk_pred ~qv "_co" e1e2 ], None ]
      (mk_imp
	(mk_eq_true (mk_pred ~qv "_co" e1e2))
	(mk_lt (mk_fun ~qv "_propi" e1) (mk_fun ~qv "_propi" e2))) in
	(* (mk_eq_true (mk_pred ~qv "_co_U_prop" e1e2))) in *)
    Queue.push axiom_co_U_prop_1 axioms;

    let axiom_co_U_prop_2 = mk_axiom "axiom_co_U_prop_2" [] ety2
      [ [ mk_pred ~qv "_fence" e1e2 ], None ]
      (mk_imp
    	(mk_eq_true (mk_pred ~qv "_fence" e1e2))
	(mk_lt (mk_fun ~qv "_propi" e1) (mk_fun ~qv "_propi" e2))) in
    	(* (mk_eq_true (mk_pred ~qv "_co_U_prop" e1e2))) in *)
    Queue.push axiom_co_U_prop_2 axioms;

    (* let axiom_co_U_prop_t = mk_axiom "axiom_co_U_prop_t" [] ety3 *)
    (*   [ [ mk_pred ~qv "_co_U_prop" e1e2 ; *)
    (* 	  mk_pred ~qv "_co_U_prop" e2e3 ], None ] *)
    (*   (mk_imp *)
    (* 	(mk_and *)
    (* 	  (mk_eq_true (mk_pred ~qv "_co_U_prop" e1e2)) *)
    (* 	  (mk_eq_true (mk_pred ~qv "_co_U_prop" e2e3))) *)
    (* 	(mk_eq_true (mk_pred ~qv "_co_U_prop" e1e3))) in *)
    (* Queue.push axiom_co_U_prop_t axioms *)

    let axiom_po_loc_U_com = mk_axiom "axiom_po_loc_U_com" [] ety2
      [ [ mk_pred ~qv "_po_loc_U_com" e1e2 ], None ]
      (mk_imp
	(mk_eq_true (mk_pred ~qv "_po_loc_U_com" e1e2))
	(mk_lt (mk_fun ~qv "_sci" e1) (mk_fun ~qv "_sci" e2))) in
    Queue.push axiom_po_loc_U_com axioms;

    let axiom_co_U_prop = mk_axiom "axiom_co_U_prop" [] ety2
      [ [ mk_pred ~qv "_co_U_prop" e1e2 ], None ]
      (mk_imp
	(mk_eq_true (mk_pred ~qv "_co_U_prop" e1e2))
	(mk_lt (mk_fun ~qv "_propi" e1) (mk_fun ~qv "_propi" e2))) in
    Queue.push axiom_co_U_prop axioms
 *)
