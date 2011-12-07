
open Format

type ty = Ty.t
exception AlreadyDeclared of Hstring.t
exception Undefined of Hstring.t

let type_int = Ty.Tint
let type_bool = Ty.Tbool

module H = Hstring.H

module Typing = struct

  let decl_types = H.create 17
  let decl_symbs = H.create 17

  let declare_constructor ty c = 
    if H.mem decl_symbs c then raise (AlreadyDeclared c);
    H.add decl_symbs c 
      (Symbols.name ~kind:Symbols.Constructor c, [], ty)
      
  let declare_type n l = 
    if H.mem decl_types n then raise (AlreadyDeclared n);
    match l with
      | [] -> 
	  H.add decl_types n (Ty.Tabstract n)
      | _ -> 
	  let ty = Ty.Tsum (n, l) in
	  H.add decl_types n ty;
	  List.iter (fun c -> declare_constructor ty c) l

  let declare_name f args ret  = 
    if H.mem decl_symbs f then raise (AlreadyDeclared f);
    H.add decl_symbs f (Symbols.name f, args, ret)

end

module Term = struct

  type term = Term.t
  type operator = Plus | Minus | Mult | Div | Modulo

  let vrai = Term.vrai
  let faux = Term.faux

  let make_int = Term.int 

  let make_app s l = 
    try
      let (sb, _, ty) = H.find Typing.decl_symbs s in
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
  type formula = 
    | Lit of Literal.LT.t  
    | Comb of combinator * formula list

  let make_lit cmp l = 
    let lit = 
      match cmp, l with
	| Eq, [t1; t2] -> 
	    Literal.Eq (t1, t2)
	| Neq, [t1; t2] -> 
	    Literal.Distinct (false, [t1; t2])
	| Le, [t1; t2] ->
	    Literal.Builtin (true, Hstring.make "<=", [t1; t2])
	| Lt, [t1; t2] ->
	    Literal.Builtin (true, Hstring.make "<", [t1; t2])
	| _ -> assert false
    in
    Lit (Literal.LT.make lit)

  let rec sform = function
    | Comb (Not, [Comb (Not, [f])]) -> f
    | Comb (Not, [Comb (Or, [f1; f2])]) -> 
	Comb (And, [sform f1; sform f2])
    | Comb (Not, [Comb (And, [f1; f2])]) ->  
	Comb (Or, [sform f1; sform f2])
    | Comb (Not, [Comb (Imp, [f1; f2])]) -> 
	Comb (And, [sform f1; sform (Comb (Not, [f2]))])
    | Comb (And, [f1; f2]) -> 
	Comb (And, [sform f1; sform f2])
    | Comb (Or, [f1; f2]) -> 
	Comb (Or, [sform f1; sform f2])
    | Comb (Imp, [f1; f2]) -> 
	Comb (Or, [sform (Comb (Not, [f1])); sform f2])
    | f -> f

  let make_formula comb l = Comb (comb, l)

  let rec cnf f = 
    match f with
      | Comb (Or, [g; d]) -> 
	  begin
	    match cnf g, cnf d with
	      | g' , Comb (And, [d1; d2]) -> 
		  let f1 = cnf (Comb (Or, [g'; d1])) in
		  let f2 = cnf (Comb (Or, [g'; d2])) in
		  Comb (And, [f1; f2])
	      | Comb (And, [g1; g2]), d' -> 
		  let f1 = cnf (Comb (Or, [g1; d'])) in
		  let f2 = cnf (Comb (Or, [g2; d'])) in
		  Comb (And, [f1; f2])
	      | _ , _ -> f
	  end
      | Comb (And, [g; d]) -> 
	  Comb (And, [cnf g; cnf d])
      | f -> f    

  let rec unfold mono f = 
    match f with
      | Lit a -> a::mono 
      | Comb (Not, [Lit a]) -> 
	  (Literal.LT.neg a)::mono
      | Comb (Or, [f1; f2]) -> 
	  unfold (unfold mono f1) f2
      | _ -> assert false
	  
  let rec init monos f = 
    match f with
      | Comb (And, [f1; f2]) -> 
	  init (init monos f1) f2
      | f -> (unfold [] f)::monos
	
  let make_cnf f = 
    let sfnc = cnf (sform f) in
    init [] sfnc

end

include Typing
include Term
include Formula

exception Sat 
exception Unsat of Explanation.t 
exception IDontknow

let clear () = Solver.clear ()

let assume f = 
  try Solver.assume (make_cnf f)
  with Solver.Unsat -> raise (Unsat Explanation.empty)

let check () =
  try Solver.solve ()
  with
    | Solver.Sat -> ()
    | Solver.Unsat -> raise (Unsat Explanation.empty)

