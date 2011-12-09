(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

open Format

exception AlreadyDeclared of Hstring.t
exception Undefined of Hstring.t

let calls = ref 0
module Time = Timer.Make(struct end)

module H = Hstring.H

module Typing = struct

  type t = Ty.t

  let decl_types = H.create 17
  let decl_symbs = H.create 17

  let type_int = 
    let tint = Hstring.make "int" in
    H.add decl_types tint Ty.Tint;
    tint

  let type_bool = 
    let tbool = Hstring.make "bool" in
    H.add decl_types tbool Ty.Tbool;
    tbool

  let type_proc = 
    let tproc = Hstring.make "proc" in
    H.add decl_types tproc Ty.Tint;
    tproc

  let declare_constructor ty c = 
    if H.mem decl_symbs c then raise (AlreadyDeclared c);
    H.add decl_symbs c 
      (Symbols.name ~kind:Symbols.Constructor c, [], ty)
      
  let declare_type (n, l) = 
    if H.mem decl_types n then raise (AlreadyDeclared n);
    match l with
      | [] -> 
	  H.add decl_types n (Ty.Tabstract n)
      | _ -> 
	  let ty = Ty.Tsum (n, l) in
	  H.add decl_types n ty;
	  List.iter (fun c -> declare_constructor n c) l

  let declare_name f args ret  = 
    if H.mem decl_symbs f then raise (AlreadyDeclared f);
    List.iter 
      (fun t -> if not (H.mem decl_types t) then raise (Undefined t)) 
      (ret::args);
    H.add decl_symbs f (Symbols.name f, args, ret)

  let find s = let _, args, ret = H.find decl_symbs s in args, ret
    
  let _ = 
    H.add decl_symbs (Hstring.make "True") 
      (Symbols.True, [], Hstring.make "bool");
    H.add decl_symbs (Hstring.make "False") 
      (Symbols.False, [], Hstring.make "bool");
    
end

module Term = struct

  type t = Term.t
  type operator = Plus | Minus | Mult | Div | Modulo

  let make_int i = Term.int (string_of_int i)

  let make_app s l = 
    try
      let (sb, _, nty) = H.find Typing.decl_symbs s in
      let ty = H.find Typing.decl_types nty in
      Term.make sb l ty
    with Not_found -> raise (Undefined s)

  let make_arith op t1 t2 = 
    let op = 
      match op with
	| Plus -> Symbols.Plus
	| Minus -> Symbols.Minus
	| Mult ->  Symbols.Mult
	| Div -> Symbols.Div
	| Modulo -> Symbols.Modulo
    in
    Term.make (Symbols.Op op) [t1; t2] Ty.Tint

end

module Formula = struct

  type comparator = Eq | Neq | Le | Lt
  type combinator = And | Or | Imp | Not
  type t = 
    | Lit of Literal.LT.t  
    | Comb of combinator * t list

  let vrai = Lit Literal.LT.vrai
  let faux = Lit Literal.LT.faux

  let make_lit cmp l = 
    let lit = 
      match cmp, l with
	| Eq, [t1; t2] -> 
	    Literal.Eq (t1, t2)
	| Neq, ts -> 
	    Literal.Distinct (false, ts)
	| Le, [t1; t2] ->
	    Literal.Builtin (true, Hstring.make "<=", [t1; t2])
	| Lt, [t1; t2] ->
	    Literal.Builtin (true, Hstring.make "<", [t1; t2])
	| _ -> assert false
    in
    Lit (Literal.LT.make lit)

  let rec sform = function
    | Comb (Not, [Lit a]) -> Lit (Literal.LT.neg a)
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
    
  let rec cnf f = 
    match f with
      | Comb (Or, l) -> 
	  begin
	    let l = List.map cnf l in
	    let l_and, l_or = 
	      List.partition (function Comb(And,_) -> true | _ -> false) l in
	    match l_and with
	      | [ Comb(And, l_conj) ] -> 
		  let u = flatten_or l_or in
		  distrib l_conj u

	      | Comb(And, l_conj) :: r ->
		  let u = flatten_or l_or in
		  cnf (Comb(Or, (distrib l_conj u)::r))

	      | _ ->  
		  begin
		    match flatten_or l_or with
		      | [] -> assert false
		      | [r] -> r
		      | v -> Comb (Or, v)
		  end
	  end
      | Comb (And, l) -> 
	  Comb (And, List.map cnf l)
      | f -> f    

  let rec unfold mono f = 
    match f with
      | Lit a -> a::mono 
      | Comb (Not, [Lit a]) -> 
	  (Literal.LT.neg a)::mono
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

  let rec print fmt f =
    match f with
      | Lit a -> Literal.LT.print fmt a
      | Comb (Not, [f]) -> 
	  fprintf fmt "not (%a)" print f
      | Comb (And, l) -> print_list "and" fmt l
      | Comb (Or, l) ->  print_list "or" fmt l
      | Comb (Imp, [f1; f2]) -> 
	  fprintf fmt "%a => %a" print f1 print f2
      | _ -> assert false
  and print_list sep fmt = function
    | [] -> ()
    | [f] -> print fmt f
    | f::l -> fprintf fmt "%a %s %a" print f sep (print_list sep) l

end

let get_time = Time.get
let get_calls () = !calls

exception Sat 
exception Unsat of Explanation.t 
exception IDontknow

let clear () = Solver.clear ()

let assume f = 
  try Solver.assume (Formula.make_cnf f)
  with Solver.Unsat -> raise (Unsat Explanation.empty)

let check ~profiling  =
  incr calls;
  if profiling then Time.start ();
  try 
    Solver.solve ();
    if profiling then Time.pause ()
  with
    | Solver.Sat -> if profiling then Time.pause ()
    | Solver.Unsat -> 
	if profiling then Time.pause ();
	raise (Unsat Explanation.empty)
