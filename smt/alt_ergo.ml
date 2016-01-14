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

type check_strategy = Lazy | Eager
                      
module H = Hstring.H
module HSet = Hstring.HSet

let all_types = H.create 17 (**)
let all_vars = H.create 17 (**)
let tso_vars = H.create 17 (**)
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

  let declare_constructor ty c = 
    if H.mem decl_symbs c then raise (Error (DuplicateSymb c));
    H.add decl_symbs c 
      (Symbols.name ~kind:Symbols.Constructor c, [], ty)

  let declare t constrs =
    H.add all_types t constrs; (* Added *)
    if H.mem decl_types t then raise (Error (DuplicateTypeName t));
    match constrs with
      | [] -> 
	  H.add decl_types t (Ty.Tabstract t)
      | _ -> 
	  let ty = Ty.Tsum (t, constrs) in
	  H.add decl_types t ty;
	  List.iter (fun c -> declare_constructor t c) constrs

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

  let declare ?(tso=false) f args ret =
    if H.mem decl_symbs f then raise (Error (DuplicateTypeName f));
    H.add all_vars f (Symbols.name f, args, ret); (* Added *) (* Needed ?*)
    if tso then H.add tso_vars f (Symbols.name f, args, ret); (* Added *)
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

  let make_event_val e =
    let s = (fst e.Event.var) in
    try
      let (_, _, nty) = H.find decl_symbs s in
      let ty = H.find decl_types nty in
      let sb = Symbols.name (Hstring.make ("e(" ^ Event.name e ^ ").val")) in 
      Term.make sb [] ty
    with Not_found -> raise (Error (UnknownSymb s))

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
    match phi with
      | Lit a -> Literal.LT.print fmt a
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

  let check_strategy = Eager

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
      all_events := events :: !all_events;
      formula := (Formula.make_cnf f) :: !formula;
      (*CSolver.assume (Formula.make_cnf f) id;*)
      Time.pause ()
    with Solver.Unsat ex ->
      Time.pause ();
      raise (Unsat [] (*(export_unsatcore2 ex)*))

 	      let typeof t =
    let t = (Hstring.view t) in
    if String.compare t "proc" = 0 then "int" else t

  let print_type fmt t =
    fprintf fmt "%s" (typeof t)

  let print_list_sep sep pfun fmt = function
    | [] -> ()
    | e :: l -> pfun fmt e;
		List.iter (fun e -> fprintf fmt " %s %a" sep pfun e) l

  let print_clause fmt c =
    fprintf fmt "(%a)" (print_list_sep "or" Literal.LT.print) c

  let print_cnf fmt cnf =
    print_list_sep "and" print_clause fmt cnf

  let replace str s1 s2 =
    Str.global_replace (Str.regexp_string s1) s2 str

  let gen_filename =
    let cnt = ref 0 in
    fun name ext ->
      cnt := !cnt + 1;
      name ^ (string_of_int !cnt) ^ ext
    
  let check ?(fp=false) () =
    incr calls;
    Time.start ();
    try
      let filename = gen_filename "formula_" ".why" in
      let file = open_out filename in
      let filefmt = formatter_of_out_channel file in

      (* Print all types *)
      H.iter (fun t cl -> match cl with
        | [] -> fprintf filefmt "type %a\n" Hstring.print t
        | _ -> fprintf filefmt "type %a = %a\n" Hstring.print t
		       (print_list_sep "|" Hstring.print) cl
      ) all_types;

      (* Print all variables *) (* should not print TSO variables *)
      H.iter (fun f (fx, args, ret) ->
        fprintf filefmt "logic %s :%a %s\n" (replace (Hstring.view f) "#" "p")
          (fun fmt -> List.iter (fun a -> fprintf fmt " %s ->" (typeof a))) args
	  (typeof ret)
      ) all_vars;

      (* Print TSO declarations *)
      Event.print_decls filefmt fp tso_vars !all_events;

      (* Print formula *)
      fprintf filefmt "goal g: true\n";
      List.iter (fun cnf ->
	fprintf str_formatter " and %a\n" print_cnf cnf;
	let t = flush_str_formatter () in
	let t = replace t "#" "p" in
	let t = replace t "True" "true" in
	let t = replace t "False" "false" in
	fprintf filefmt "%s" t;
      ) (List.rev !formula);

      (* Print TSO relations *)
      if not fp then
	Event.print_rels filefmt !all_events;

      (* Output file *)
      flush file;
      close_out file;

      (* Call solver and check result *)
      eprintf "-------------> Calling Alt-Ergo on %s <-------------\n" filename;
      let output = Util.syscall ("alt-ergo -sat-mode " ^ filename) in
      if String.compare output "unsat\n" = 0 then
        raise (Solver.Unsat [])
      else if String.compare output "unknown (sat)\n" <> 0 then
	failwith "Error calling SMT solver";
      (*if String.compare output "unsat\n" = 0 then exit 0;*)
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
