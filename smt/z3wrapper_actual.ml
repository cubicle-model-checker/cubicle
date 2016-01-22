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

open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.Goal
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real

open Format

type error = 
  | DuplicateTypeName of Hstring.t
  | DuplicateSymb of Hstring.t
  | UnknownType of Hstring.t
  | UnknownSymb of Hstring.t

exception Error of error

type symbol_kind = TAbstract | TConstructor
type check_strategy = Lazy | Eager

module H = Hstring.H
module HSet = Hstring.HSet

let decl_types = H.create 17
let decl_symbs = H.create 17

let htrue = Hstring.make "True"
let hfalse = Hstring.make "False"

let global_context =
  mk_context [("model", "false");
              ("proof", "false");
              ("unsat_core", "true");
              ("auto_config","true")]

module Type = struct

  type t = Hstring.t
  
  let equal = Hstring.equal

  let type_int = 
    (* eprintf "type_int@."; *)
    let tint = Hstring.make "int" in
    let z3int = Integer.mk_sort global_context in 
    H.add decl_types tint z3int;
    tint

  let type_real = 
    (* eprintf "type_real@."; *)
    let treal = Hstring.make "real" in
    let z3real = Real.mk_sort global_context in
    H.add decl_types treal z3real;
    treal

  let type_bool =
    (* eprintf "type_bool@."; *)
    let tbool = Hstring.make "bool" in
    let z3bool = Boolean.mk_sort global_context in
    H.add decl_types tbool z3bool;
    tbool

  let type_proc =
    (* eprintf "type_proc@."; *)
    let tproc = Hstring.make "proc" in
    let z3int = Integer.mk_sort global_context in 
    H.add decl_types tproc z3int;
    tproc

  let declare_constructor ty c f =
    (* eprintf "declare_constructor@."; *)
    if H.mem decl_symbs c then raise (Error (DuplicateSymb c));
    H.add decl_symbs c (f, TConstructor, [], ty)

  let declare t constrs =
    (* eprintf "declare@."; *)
    if H.mem decl_types t then raise (Error (DuplicateTypeName t));
    match constrs with
    | [] ->
      let ty = Sort.mk_uninterpreted_s global_context (Hstring.view t) in
      H.add decl_types t ty
    | _ ->
      let ty = Enumeration.mk_sort_s global_context
          (Hstring.view t) (List.map Hstring.view constrs) in
      H.add decl_types t ty;
      List.iter2 (declare_constructor t) constrs (Enumeration.get_const_decls ty)

  let all_constructors () =
    (* eprintf "all_constructors@."; *)
    H.fold (fun h c acc ->
        match c with
        | _, TConstructor, _, _ -> h :: acc
        | _ -> acc
    ) decl_symbs [htrue; hfalse]

  let constructors ty =
    (* eprintf "constructors of %a@." Hstring.print ty; *)
    if Hstring.equal ty type_bool then [htrue; hfalse]
    else
      let z3_ty = H.find decl_types ty in
      if Sort.get_sort_kind z3_ty = Z3enums.DATATYPE_SORT then
        Enumeration.get_const_decls z3_ty
        |> List.map (fun f ->
            f
            |> FuncDecl.get_name
            |> Symbol.get_string
            |> Hstring.make)
      else []

  let declared_types () =
    H.fold (fun ty _ acc -> ty :: acc) decl_types []

end

module Symbol = struct
    
  type t = Hstring.t

  let declare ?(tso=false) f args ret =
    (* eprintf "declare@."; *)
    if H.mem decl_symbs f then raise (Error (DuplicateTypeName f));
    let z3_args = List.map (fun t ->
        try H.find decl_types t
        with Not_found -> raise (Error (UnknownType t));
      ) args in
    let z3_ret =
      try H.find decl_types ret
      with Not_found -> raise (Error (UnknownType ret)) in
    let z3_f =
      FuncDecl.mk_func_decl_s global_context (Hstring.view f) z3_args z3_ret in
    H.add decl_symbs f (z3_f, TAbstract, args, ret)

  let type_of s =
    (* eprintf "type_of@."; *)
    let _, _, args, ret = H.find decl_symbs s in args, ret

  let declared s =
    (* eprintf "declared@."; *)
    let res = H.mem decl_symbs s in
    if not res then begin 
      eprintf "Not declared : %a in@." Hstring.print s;
      H.iter (fun hs (sy, _, _, _) ->
	eprintf "%a (=?%b) -> %s@." Hstring.print hs 
	  (Hstring.compare hs s = 0)
	  (FuncDecl.get_name sy |> Symbol.get_string))
	  decl_symbs;
      end;
      res

  let not_builtin ty =
    (* eprintf "not_builtin@."; *)
    Hstring.equal ty Type.type_proc ||
    not (Hstring.equal ty Type.type_int || Hstring.equal ty Type.type_real ||
	   Hstring.equal ty Type.type_bool || Hstring.equal ty Type.type_proc)
    
  let has_abstract_type s =
    (* eprintf "has_abstract_type@."; *)
    let _, ret = type_of s in
    H.find decl_types ret |> Sort.get_sort_kind = Z3enums.UNINTERPRETED_SORT

  let has_infinite_type s =
    (* eprintf "has_infinite_type@."; *)
    let _, ret = type_of s in
    Hstring.equal ret Type.type_real ||
    Hstring.equal ret Type.type_int ||
    (* Hstring.equal ret Type.type_proc || *)
    H.find decl_types ret |> Sort.get_sort_kind = Z3enums.UNINTERPRETED_SORT
     
  let has_type_proc s =
    (* eprintf "has_type_proc@."; *)
    Hstring.equal (snd (type_of s)) Type.type_proc

  let fd_true =
    (* eprintf "fd_true@."; *)
    Boolean.mk_true global_context |> Expr.get_func_decl
  let fd_false =
    (* eprintf "fd_false@."; *)
    Boolean.mk_false global_context |> Expr.get_func_decl
  
  let _ =
    (* eprintf "_@."; *)
    H.add decl_symbs htrue (fd_true, TConstructor, [], Type.type_bool);
    H.add decl_symbs hfalse (fd_false, TConstructor, [], Type.type_bool);
    
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
	  Format.eprintf "%a = {%a}@." Hstring.print x hset_print c) 
	constructors
	
	
  let get_variants = H.find constructors
    
  let set_of_list = List.fold_left (fun s x -> HSet.add x s) HSet.empty 

  let init l = 
    compute ();
    List.iter 
      (fun (x, nty) -> 
	 if not (H.mem constructors x) then
           let ty = H.find decl_types nty in
           if Sort.get_sort_kind ty = Z3enums.DATATYPE_SORT then
	     H.add constructors x (set_of_list (Type.constructors nty))
      ) l;
    H.clear assignments

  let update_decl_types s = 
    let sty = ref "|" in
    let l = ref [] in
    HSet.iter 
      (fun x ->
         let vx = Hstring.view x in 
	 sty := if !l = [] then !sty ^ vx else !sty ^ "," ^ vx;
         l := vx :: !l; 
      ) s;
    let sty = !sty ^ "}" in
    let nty = Hstring.make sty in
    let ty = Enumeration.mk_sort_s global_context sty (List.rev !l) in
    H.replace decl_types nty ty;
    nty

  let close () = 
    compute ();
    H.iter (fun x s -> 
	let nty = update_decl_types s in
        let sy, _, args, _ = H.find decl_symbs x in
	H.replace decl_symbs x (sy, TConstructor, args, nty))
      constructors
      
end
  
module Term = struct

  type t = Expr.expr
  type operator = Plus | Minus | Mult | Div | Modulo

  let make_int i = Integer.mk_numeral_s global_context (Num.string_of_num i)

  let make_real r = Real.mk_numeral_s global_context (Num.string_of_num r)

  let make_app s l =
    try
      let (sb, _, _, _) = H.find decl_symbs s in
      Expr.mk_app global_context sb l
    with Not_found -> raise (Error (UnknownSymb s))

  let t_true = Boolean.mk_true global_context
  let t_false = Boolean.mk_false global_context

  let make_arith op t1 t2 = match op with
    | Plus -> mk_add global_context [t1; t2]
    | Minus -> mk_sub global_context [t1; t2]
    | Mult -> mk_mul global_context [t1; t2]
    | Div -> mk_div global_context t1 t2
    | Modulo -> failwith "modulo not supported by Z3 for now"

  let make_event_val e =
    failwith "Z3Wrapper_actual.Term.make_event_val TODO"

  let is_int = is_int

  let is_real = is_real

end

module Formula = struct

  type comparator = Eq | Neq | Le | Lt
  type combinator = And | Or | Imp | Not

  type literal = Expr.expr
  type t = Expr.expr
  
  let rec print fmt phi = fprintf fmt "%s" (Expr.to_string phi)

  let f_true = Boolean.mk_true global_context
  let f_false = Boolean.mk_false global_context

  let make_lit cmp l = match cmp, l with
      | Eq, [t1; t2] -> mk_eq global_context t1 t2
      | Neq, ts -> mk_distinct global_context ts
      | Le, [t1; t2] -> mk_le global_context t1 t2
      | Lt, [t1; t2] -> mk_lt global_context t1 t2
      | _ -> assert false

  (* TODO : simplifications, see [Expr.simplify] *)

  let make comb l = match comb with
    | And -> mk_and global_context l
    | Or -> mk_or global_context l
    | Not ->
      (match l with [a] -> mk_not global_context a | _ -> assert false)
    | Imp ->
      match l with
      | [a; b] -> mk_or global_context [mk_not global_context a; b]
      | _ -> assert false


  let make_cnf f =
    failwith "CNF unimplemented"

  let make_event_desc e =
    failwith "Z3Wrapper_actual.Formula.make_event_desc TODO"

  let make_acyclic_rel e =
    failwith "Z3Wrapper_actual.Formula.make_acyclic_rel TODO"

  let make_po (e1, e2) =
    failwith "Z3Wrapper_actual.Formula.make_po TODO"

  let make_co (e1, e2) =
    failwith "Z3Wrapper_actual.Formula.make_co TODO"

  let make_rf_cands rfl =
    failwith "Z3Wrapper_actual.Formula.make_rf_cands TODO"

  let make_fence (e1, e2) =
    failwith "Z3Wrapper_actual.Formula.make_fence TODO"

end

exception Unsat of int list

let set_cc b = ()
let set_arith _ = ()
let set_sum _ = ()

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

  let calls = ref 0
  module Time = Timer.Make (Options)

  let get_time = Time.get
  let get_calls () = !calls

  (* TODO use hash of z3 expr *)
  let assertions = Hashtbl.create 17
  
  let solver = 
    (* eprintf "mk_solver@."; *)
    mk_simple_solver global_context

  
  (* let _ = *)
  (*   eprintf "Z3 help:\n%s@." (Solver.get_help solver) *)

  let clear () =
    (* eprintf "clear@."; *)
    Hashtbl.clear assertions;
    reset solver

  let assume ?(events=Event.empty_struct) ~id f =
    (* eprintf "assume@."; *)
    Time.start ();
    Solver.add solver [f];
    Hashtbl.add assertions f id;
    Time.pause ()

  let check ?(fp=false) () =
    (* eprintf "check@."; *)
    incr calls;
    Time.start ();
    let st = Solver.check solver [] in
    Time.pause ();
    match st with
    | SATISFIABLE -> ()
    | UNKNOWN -> failwith "Z3 returned unknown"
    | UNSATISFIABLE ->
      let uc = get_unsat_core solver |> List.map (Hashtbl.find assertions) in
      raise (Unsat uc)

  let entails f =
    incr calls;
    Time.start ();
    let nf = Formula.make Formula.Not [f] in
    let tracker = Expr.mk_fresh_const global_context "tracker"
        (Boolean.mk_sort global_context) in
    let tracker_imp_nf = Formula.make Formula.Imp [tracker; nf] in
    Solver.add solver [tracker_imp_nf];
    let st = Solver.check solver [tracker] in
    Time.pause ();
    match st with
    | SATISFIABLE -> false
    | UNKNOWN -> failwith "Z3 returned unknown"
    | UNSATISFIABLE -> true

  let push () = Solver.push solver

  let pop () = Solver.pop solver 1
  
end
