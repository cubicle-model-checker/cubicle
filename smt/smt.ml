
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

  let vrai = Lit(Literal.LT.vrai)
  let faux = Lit(Literal.LT.faux)

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

  let make comb l = Comb (comb, l)

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
