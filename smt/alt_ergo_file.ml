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

module TTerm = Term

let all_types = ref []
let all_vars = H.create 17

let decl_types = H.create 17
let decl_symbs = H.create 17

let htrue = Hstring.make "True"
let hfalse = Hstring.make "False"

module Type = struct

  type t = Hstring.t

  let equal = Hstring.equal

  let type_int = 
    let tint = Hstring.make "int" in
    H.add decl_types tint Ty.Tint;
    tint

  let type_real = 
    let treal = Hstring.make "real" in
    H.add decl_types treal Ty.Treal;
    treal

  let type_bool = 
    let tbool = Hstring.make "bool" in
    H.add decl_types tbool Ty.Tbool;
    tbool

  let type_proc = 
    let tproc = Hstring.make "proc" in
    H.add decl_types tproc Ty.Tint;
    tproc

  let type_prop = 
    let tprop = Hstring.make "prop" in
    H.add decl_types tprop Ty.Tbool;
    tprop

  let declare_constructor ty c = 
    if H.mem decl_symbs c then raise (Error (DuplicateSymb c));
    H.add decl_symbs c 
      (Symbols.name ~kind:Symbols.Constructor c, [], ty)

  let declare t constrs = 
    if H.mem decl_types t then raise (Error (DuplicateTypeName t));
    match constrs with
      | [] -> 
	  let ty = Ty.Tabstract t in
          all_types := ty :: !all_types;
	  H.add decl_types t ty
      | _ -> 
	  let ty = Ty.Tsum (t, constrs) in
          all_types := ty :: !all_types;
	  H.add decl_types t ty;
	  List.iter (fun c -> declare_constructor t c) constrs

  let declare_field ty f =
    if H.mem decl_symbs f then raise (Error (DuplicateSymb f));
    H.add decl_symbs f (Symbols.Op (Symbols.Access f), [], ty)

  let declare_record t fields =
    if H.mem decl_types t then raise (Error (DuplicateTypeName t));
    let tfields = List.map (fun (f, ty) -> (f, H.find decl_types ty)) fields in
    let ty = Ty.Trecord (t, tfields) in
    all_types := ty :: !all_types;
    H.add decl_types t ty;
    List.iter (fun (f, ty) -> declare_field ty f) fields

  let all_constructors () =
    H.fold (fun _ c acc -> match c with
      | Symbols.Name (h, Symbols.Constructor), _, _ -> h :: acc
      | _ -> acc
    ) decl_symbs [htrue; hfalse]

  let constructors ty =
    if Hstring.equal ty type_bool then [htrue; hfalse]
    else match H.find decl_types ty with
      | Ty.Tsum (_ , cstrs) -> cstrs
      | _ -> []

  let declared_types () =
    H.fold (fun ty _ acc -> ty :: acc) decl_types []

end

module Symbol = struct
    
  type t = Hstring.t

  let declare f args ret  = 
    if H.mem decl_symbs f then raise (Error (DuplicateTypeName f));
    H.add all_vars f (Symbols.name f, args, ret);
    List.iter 
      (fun t -> 
	if not (H.mem decl_types t) then raise (Error (UnknownType t)) )
      (ret::args);
    H.add decl_symbs f (Symbols.name f, args, ret)

  let type_of s = let _, args, ret = H.find decl_symbs s in args, ret

  let declared s = 
    let res = H.mem decl_symbs s in
    if not res then begin 
      eprintf "Not declared : %a in@." Hstring.print s;
      H.iter (fun hs (sy, _, _) ->
	eprintf "%a (=?%b) -> %a@." Hstring.print hs 
	  (Hstring.compare hs s = 0)
	  Symbols.print sy)
	  decl_symbs;
      end;
      res

  let not_builtin ty = Hstring.equal ty Type.type_proc ||
    not (Hstring.equal ty Type.type_int || Hstring.equal ty Type.type_real ||
	   Hstring.equal ty Type.type_bool || Hstring.equal ty Type.type_proc)
    
  let has_abstract_type s =
    let _, ret = type_of s in
    match H.find decl_types ret with
      | Ty.Tabstract _ -> true
      | _ -> false

  let has_infinite_type s =
    let _, ret = type_of s in
    Hstring.equal ret Type.type_real ||
    Hstring.equal ret Type.type_int ||
    (* Hstring.equal ret Type.type_proc || *)
    match H.find decl_types ret with
      | Ty.Tabstract _ -> true
      | _ -> false
     
  let has_type_proc s =
    Hstring.equal (snd (type_of s)) Type.type_proc
      
  let _ = 
    H.add decl_symbs htrue (Symbols.True, [], Type.type_bool);
    H.add decl_symbs hfalse (Symbols.False, [], Type.type_bool);
    
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
	    | Ty.Tsum (_, l) ->
	      H.add constructors x (set_of_list l)
	    | _ -> ()) l;
    H.clear assignments

  let update_decl_types s old_ty x =
    let new_ty = Hstring.(view old_ty ^ "_" ^ view x |> make) in
    let l = HSet.elements s in
    let ty = Ty.Tsum (new_ty, (* List.rev *) l) in
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

  type t = Term.t
  type operator = Plus | Minus | Mult | Div | Modulo

  let make_int i = Term.int (Num.string_of_num i)

  let make_real r = Term.real (Num.string_of_num r)

  let make_app s l =
    try
      let (sb, _, nty) = H.find decl_symbs s in
      let ty = H.find decl_types nty in
      Term.make sb l ty
    with Not_found -> raise (Error (UnknownSymb s))

  let t_true = Term.vrai
  let t_false = Term.faux

  let make_arith op t1 t2 = 
    let op = 
      match op with
	| Plus -> Symbols.Plus
	| Minus -> Symbols.Minus
	| Mult ->  Symbols.Mult
	| Div -> Symbols.Div
	| Modulo -> Symbols.Modulo
    in
    let ty = 
      if Term.is_int t1 && Term.is_int t2 then Ty.Tint
      else if Term.is_real t1 && Term.is_real t2 then Ty.Treal
      else assert false
    in
    Term.make (Symbols.Op op) [t1; t2] ty

  let is_int = Term.is_int

  let is_real = Term.is_real

end

module Formula = struct

  type comparator = Eq | Neq | Le | Lt
  type combinator = And | Or | Imp | Not

  type literal = Literal.LT.t
  
  type t = 
    | Lit of literal
    | Comb of combinator * t list

  let rec print fmt phi = 
    let rec print_diff fmt t1 = function
      | [] -> assert false
      | [t2] -> TTerm.print fmt t1;
		Format.fprintf fmt " <> ";
		TTerm.print fmt t2
      | t2 :: tl -> print_diff fmt t1 [t2];
		    Format.fprintf fmt " and ";
		    print_diff fmt t1 tl in
    let rec print_all_diff fmt = function
      | [] | [_] -> Format.fprintf fmt "true"
      | t :: tl -> print_diff fmt t tl;
		   Format.fprintf fmt " and ";
		   print_all_diff fmt tl in
    match phi with
      | Lit a ->
         let l = Literal.LT.view a in
	 begin match l with
	   | Literal.Distinct (b, al) ->
	       if b then Format.fprintf fmt "not (";
	       print_all_diff fmt al;
	       if b then Format.fprintf fmt ")";
	   | _ -> Literal.LT.print fmt a
	 end
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

  let f_true = Lit Literal.LT.vrai
  let f_false = Lit Literal.LT.faux

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
  | Comb (Not, [Lit a]) -> [[Literal.LT.neg a]]
  | _ -> assert false


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

  (* let make_cnf f = mk_cnf (sform f) *)

end

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

  let axioms = ref ""

  let init_axioms () =
    if Options.model = Options.SC then ()
    else axioms :=
(*"
axiom po_loc :
  forall p1, p2, e1, e2 : int [_po_loc(p1,e1,p2,e2)].
  _po_loc(p1, e1, p2, e2)
   -> _sci(p1, e1) < _sci(p2, e2)

axiom co_1 :
  forall p1, p2, e1, e2 : int [_co(p1,e1,p2,e2)].
  _co(p1, e1, p2, e2)
   -> _sci(p1, e1) < _sci(p2, e2)
(*axiom co_1 :
  forall p1, p2, e1, e2 : int [_coi(p1,e1),_coi(p2,e2)].
  _coi(p1, e1) < _coi (p2, e2, s2)
   -> _sci(p1, e1) < _sci(p2, e2)*)

axiom rf :
  forall p1, e1, p2, e2 : int [_rf(p1,e1,p2,e2)].
  _rf(p1, e1, p2, e2)
   -> _sci(p1, e1) < _sci(p2, e2)

axiom ppo :
  forall p1, p2, e1, e2 : int [_ppo(p1,e1,p2,e2)].
  _ppo(p1, e1, p2, e2)
   -> _propi(p1, e1) < _propi(p2, e2)

axiom fence :
  forall p1, p2, e1, e2 : int [_fence(p1,e1,p2,e2)].
  _fence(p1, e1, p2, e2)
   -> _propi(p1, e1) < _propi(p2, e2)

axiom co_2 :
  forall p1, e1, p2, e2 : int [_co(p1,e1,p2,e2)].
  _co(p1, e1, p2, e2)
  -> _propi(p1, e1) < _propi(p2, e2)
(*axiom co_2 :
  forall p1, e1, p2, e2 : int [_coi(p1,e1),_coi(p2,e2)].
  _coi(p1, e1) < _coi(p2, e2)
  -> _propi(p1, e1) < _propi(p2, e2)*)

axiom rfe :
  forall p1, p2, e1, e2 : int [_rf(p1,e1,p2,e2)].
  _rf(p1, e1, p2, e2) and p1 <> p2
  -> _propi(p1, e1) < _propi(p2, e2)

axiom fr :
  forall pr, pw1, pw2, r, w1, w2 : int
    [_rf(pw1,w1,pr,r),_co(pw1,w1,pw2,w2)].
  _rf(pw1, w1, pr, r) and _co(pw1, w1, pw2, w2)
  -> _sci(pr, r) < _sci(pw2, w2) and _propi(pr, r) < _propi(pw2, w2)
(*axiom fr :
  forall pr, pw1, pw2, r, w1, w2 : int
    [_rf(pw1,w1,pr,r),_coi(pw1,w1),_coi(pw2,w2)].
  _rf(pw1, w1, pr, r) and _coi(pw1, w1) < _coi(pw2, w2)
  -> _sci(pr, r) < _sci(pw2, w2) and _propi(pr, r) < _propi(pw2, w2)*)

axiom sync :
  forall p1, p2, e1, e2 : int [_sync(p1,e1,p2,e2)].
  _sync(p1, e1, p2, e2)
   -> _sci(p1, e1) = _sci(p2, e2) and _propi(p1, e1) = _propi(p2, e2)"*)

(*"
axiom co_1 :
  forall e1, e2 : int [_co(e1,e2)].
  _co(e1, e2)
   -> _sci(e1) < _sci(e2)

axiom co_2 :
  forall e1, e2 : int [_co(e1,e2)].
  _co(e1, e2)
  -> _propi(e1) < _propi(e2)

axiom fr :
  forall r, w1, w2 : int
    [_rf(w1,r),_co(w1,w2)].
  _rf(w1, r) and _co(w1, w2)
  -> _sci(r) < _sci(w2) and _propi(r) < _propi(w2)"*)

  ""

  let typeof t =
    let t = (Hstring.view t) in
    if String.compare t "proc" = 0 then "int" else t

  let print_type fmt t =
    fprintf fmt "%s" (typeof t)

  let print_list_sep sep pfun fmt = function
    | [] -> ()
    | e :: l -> pfun fmt e;
		List.iter (fun e -> fprintf fmt " %s %a" sep pfun e) l

  let print_hset_sep sep pfun fmt set =
    let first = ref true in
    Hstring.H.iter (fun k v ->
      if !first then begin pfun fmt (k, v); first := false end
    else fprintf fmt " %s %a" sep pfun (k, v)) set

  let print_clause fmt c =
    let pfun fmt l = Formula.print fmt (Formula.Lit l) in
    fprintf fmt "(%a)" (print_list_sep "or" pfun) c

  let print_cnf fmt cnf =
    print_list_sep "and" print_clause fmt cnf

  let replace str s1 s2 =
    Str.global_replace (Str.regexp_string s1) s2 str

  let print_var_name fmt v =
    fprintf fmt "_V%s" (replace (Hstring.view v) "#" "p")

  let gen_filename =
    let cnt = ref 0 in
    fun name ext ->
      cnt := !cnt + 1;
      name ^ (string_of_int !cnt) ^ ext

  let formula = ref []

  let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

  (***********************************************)

  let check_strategy = Lazy

  let push_stack = Stack.create ()
  
  let calls = ref 0
  module Time = Timer.Make (Options_)

  let get_time = Time.get
  let get_calls () = !calls

  (*module CSolver = Solver.Make (Options_)*)

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

      (* Create .why file *)
      let prefix = if fp then "formula_fp_" else "formula_sat_" in
      let filename = gen_filename prefix ".why" in
      let file = open_out filename in
      let filefmt = formatter_of_out_channel file in

      (* Print all types *)
      let print_field fmt (f, t) =
      	fprintf fmt "%a : %a" Hstring.print f Ty.print t in
      List.iter (fun ty -> match ty with
        | Ty.Tabstract t -> fprintf filefmt "type %a\n" Hstring.print t
        | Ty.Tsum (t, cl) ->
	   fprintf filefmt "type %a = %a\n" Hstring.print t
      		   (print_list_sep "|" Hstring.print) cl
        | Ty.Trecord (t, fl) ->
	   fprintf filefmt "type %a = { %a }\n" Hstring.print t
      		   (print_list_sep ";" print_field) fl
	| _ -> failwith "AltErgoFile.check : invalid type"
      ) (List.rev !all_types); (* allows to skip variants *)
      fprintf filefmt "\n";

      (* Print all variables *)
      H.iter (fun f (fx, args, ret) ->
	(*if not (Weakmem.is_weak f) then*)
          fprintf filefmt "logic %s : %a%s\n" (replace (Hstring.view f) "#" "p")
	  (print_list_sep "," print_type) args
	  ((if args = [] then " " else " -> ") ^ (typeof ret))
      ) all_vars;
      fprintf filefmt "\n";

      (* Print Weak Memory Axomatization *)
      if not fp then fprintf filefmt "%s\n\n" !axioms;
      (* fprintf filefmt "%s\n\n" !axioms; *)

      (* Print formula *)
      fprintf filefmt "goal g: not (true\n";
      List.iter (fun cnf ->
	fprintf str_formatter " and %a\n" print_cnf cnf;
	let t = flush_str_formatter () in
	let t = replace t "#" "p" in
	let t = replace t "True" "true" in
	let t = replace t "False" "false" in
	fprintf filefmt "%s" t;
      ) (List.rev !formula);
      fprintf filefmt ")\n";
	      
      (* Output file *)
      flush file;
      close_out file;

      (* Call solver and check result *)
      let output = Util.syscall ("alt-ergo " ^ filename) in
      if contains output "Valid" then raise (Solver.Unsat [])
      else if not (contains output "I don't know") then
      	failwith "Alt_ergo_file.check : error calling SMT solver";

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
    failwith "Alt_ergo_file.entails unsupported"

  let push () = (*Stack.push (save_state ()) push_stack*)
    failwith "Alt_ergo_file.push unsupported"

  let pop () = (*Stack.pop push_stack |> restore_state*)
    failwith "Alt_ergo_file.pop unsupported"

end
