(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
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
open Ast
open Atom
open Options

module T = Smt.Term
module F = Smt.Formula

module TimeF = Timer.Make (struct end)

module SMT = Smt.Make (struct end)

let proc_terms =
  List.iter 
    (fun x -> Smt.Symbol.declare x [] Smt.Type.type_proc) proc_vars;
  List.map (fun x -> T.make_app x []) proc_vars

let distinct_vars = 
  let t = Array.create max_proc F.f_true in
  let _ = 
    List.fold_left 
      (fun (acc,i) v -> 
	 if i<>0 then t.(i) <- F.make_lit F.Neq (v::acc);
	 v::acc, i+1) 
      ([],0) proc_terms 
  in
  function n -> if n = 0 then F.f_true else t.(n-1)

let order_vars =
  let t = Array.create max_proc F.f_true in
  let _ =
    List.fold_left
      (fun (acc, lf, i) v ->
        match acc with
          | v2::r ->
            let lf = (F.make_lit F.Lt [v2;v]) :: lf in
            t.(i) <- F.make F.And lf;
            v::acc, lf, i+1
          | [] -> v::acc, lf, i+1)
      ([], [], 0) proc_terms
  in
  function n -> if n = 0 then F.f_true else t.(n-1)


let make_op_arith = function Plus -> T.Plus | Minus -> T.Minus
let make_op_comp = function
  | Eq -> F.Eq
  | Lt -> F.Lt
  | Le -> F.Le
  | Neq -> F.Neq

let make_const = function
  | ConstInt i -> T.make_int i
  | ConstReal i -> T.make_real i
  | ConstName n -> T.make_app n []

let ty_const = function
  | ConstInt _ -> Smt.Type.type_int
  | ConstReal _ -> Smt.Type.type_real
  | ConstName n -> snd (Smt.Symbol.type_of n)

let rec mult_const tc c i =
 match i with
  | 0 -> 
    if ty_const c = Smt.Type.type_int then T.make_int (Num.Int 0)
    else T.make_real (Num.Int 0)
  | 1 -> tc
  | -1 -> T.make_arith T.Minus (mult_const tc c 0) tc
  | i when i > 0 -> T.make_arith T.Plus (mult_const tc c (i - 1)) tc
  | i when i < 0 -> T.make_arith T.Minus (mult_const tc c (i + 1)) tc
  | _ -> assert false

let make_arith_cs =
  MConst.fold 
    (fun c i acc ->
      let tc = make_const c in
      let tci = mult_const tc c i in
       T.make_arith T.Plus acc tci)

let make_cs cs =
  let c, i = MConst.choose cs in
  let t_c = make_const c in
  let r = MConst.remove c cs in
  if MConst.is_empty r then mult_const t_c c i
  else make_arith_cs r (mult_const t_c c i)
	 
let rec make_term = function
  | Elem (e, _) -> T.make_app e []
  | Const cs -> make_cs cs 
  | Access (a, li) -> T.make_app a (List.map (fun i -> T.make_app i []) li)
  | Arith (x, cs) -> 
      let tx = make_term x in
      make_arith_cs cs tx

let rec make_formula_set sa = 
  F.make F.And (SAtom.fold (fun a l -> make_literal a::l) sa [])

and make_literal = function
  | True -> F.f_true 
  | False -> F.f_false
  | Comp (x, op, y) ->
      let tx = make_term x in
      let ty = make_term y in
      F.make_lit (make_op_comp op) [tx; ty]
  | Ite (la, a1, a2) -> 
      let f = make_formula_set la in
      let a1 = make_literal a1 in
      let a2 = make_literal a2 in
      let ff1 = F.make F.Imp [f; a1] in
      let ff2 = F.make F.Imp [F.make F.Not [f]; a2] in
      F.make F.And [ff1; ff2]


let make_formula atoms =
  F.make F.And (Array.fold_left (fun l a -> make_literal a::l) [] atoms)

module HAA = Hashtbl.Make (ArrayAtom)

let make_formula =
  let cache = HAA.create 200001 in
  fun atoms ->
    try HAA.find cache atoms
    with Not_found ->
      let f = make_formula atoms in
      HAA.add cache atoms f;
      f

let make_disjunction nodes = F.make F.Or (List.map make_formula nodes)


let make_conjuct atoms1 atoms2 =
  let l = Array.fold_left (fun l a -> make_literal a::l) [] atoms1 in
  let l = Array.fold_left (fun l a -> make_literal a::l) l atoms2 in
  F.make F.And l


let make_init_dnfs args =
  let cdnf_sa, _ = Hashtbl.find init_instances (List.length args) in
  List.rev_map (List.rev_map make_formula_set) cdnf_sa


(**************************************************************)
(*   let all_values ty = *)
(*     try *)
(*       if Hstring.equal ty Smt.Type.type_proc then  *)
(*         List.map (fun p -> Elem(p,Var)) proc_vars *)
(*       else List.map (fun c -> Elem(c,Constr)) (Smt.Type.constructors ty) *)
(*     with Not_found -> assert false *)

(*   let type_of_term = function *)
(*     | Elem (x, _) | Access (x, _, _) -> snd (Smt.Symbol.type_of x) *)
(*     | _ -> assert false *)

(*   (\* let val_and_mask v ty = *\) *)
(*   (\*   let mask, va, _ = *\) *)
(*   (\*     List.fold_left (fun (mask, va, n) c ->  *\) *)
(*   (\*       (1 lsl n) lor mask, *\) *)
(*   (\*       (if Hstring.equal v c then (1 lsl n) lor va else va), *\) *)
(*   (\*       n + 1) *\) *)
(*   (\*       (0, 0, 0) (all_values ty) *\) *)
(*   (\*   in va, mask *\) *)

(*   let make_eq t v =  make_literal (Comp (t, Eq, v)) *)
(*     (\* | Elem (x, Glob) -> *\) *)
(*     (\*     let ty = snd (Smt.Symbol.type_of x) in *\) *)
(*     (\*     let va, mask = val_and_mask v ty in *\) *)
(*     (\*     x, va, mask *\) *)
(*     (\* | Access (a, x, Var) -> *\) *)
(*     (\*     let ty = snd (Smt.Symbol.type_of a) in *\) *)
(*     (\*     let va, mask = val_and_mask v ty in         *\) *)
(*     (\*     Hstring.make ((Hstring.view a)^(Hstring.view x)), va, mask *\) *)
(*     (\* | _ -> assert false *\) *)


(*   (\* let neg_lit (h, va, mask) = h, mask land (lnot va), mask *\) *)
(*   let neg_lit a = F.make F.Not [a] *)
    
(*   let make_neq t v = make_literal (Comp (t, Neq, v)) *)

(*   let make_dnf_literal = function *)
(*     | True -> [[make_literal True]] *)
(*     | False -> [[make_literal False]] *)

(*     | Comp (Elem (x, (Constr|Var)), Eq, Elem (y, (Constr|Var))) -> *)
(*         if Hstring.equal x y then [[make_literal True]] *)
(*         else [[make_literal False]] *)

(*     | Comp (Elem (x, (Constr|Var)), Neq, Elem (y, (Constr|Var))) -> *)
(*         if Hstring.equal x y then [[make_literal False]] *)
(*         else [[make_literal True]] *)
          
(*     | Comp (t, Eq, (Elem (_, (Constr|Var)) as v)) *)
(*     | Comp ((Elem (_, (Constr|Var)) as v), Eq, t) -> *)
(*         [[make_eq t v]] *)
          
(*     | Comp (t, Neq, (Elem (_, (Constr|Var)) as v)) *)
(*     | Comp ((Elem (_, (Constr|Var)) as v), Neq, t) -> *)
(*         [[make_neq t v]] *)

(*     | Comp (x, Eq, y) -> *)
(*         let vs_x = all_values (type_of_term x) in *)
(*         let vs_y = all_values (type_of_term y) in *)
(*         List.fold_left (fun acc vx -> *)
(*           if List.mem vx vs_y then *)
(*             [make_eq x vx; make_eq y vx] :: acc *)
(*           else acc) [] vs_x *)
          
(*     | Comp (x, Neq, y) -> *)
(*         let vs_x = all_values (type_of_term x) in *)
(*         let vs_y = all_values (type_of_term y) in *)
(*         List.fold_left (fun acc vx -> *)
(*           if List.mem vx vs_y then *)
(*             [make_eq x vx; make_neq y vx] :: acc *)
(*           else [make_eq x vx] :: acc) [] vs_x *)
          
(*     | _ -> assert false *)

(*   let make_literall a = *)
(*     List.rev_map (List.rev_map neg_lit) (make_dnf_literal (neg a))         *)

(*   let make_formula atoms = *)
(*     Array.fold_left (fun acc a -> *)
(*       List.rev_append (make_literall a) acc) *)
(*       [] atoms *)

(* module HAA = Hashtbl.Make (ArrayAtom) *)

(*   let make_formula = *)
(*     let cache = HAA.create 200001 in *)
(*     fun atoms -> *)
(*       try HAA.find cache atoms *)
(*       with Not_found -> *)
(*         let f = make_formula atoms in *)
(*         HAA.add cache atoms f; *)
(*         f *)

(*   let make_formula_set atoms = *)
(*     SAtom.fold (fun a acc -> List.rev_append (make_literall a) acc) atoms [] *)

(*   let make_neg_formula atoms = *)
(*     Array.fold_left (fun acc a -> *)
(*       List.fold_left (fun acc' l ->  *)
(*         List.rev_append (List.rev_map (fun d -> l @ d) acc) acc') *)
(*         [] (make_literall (neg a))) *)
(*       [[]] atoms *)

(*   let make_neg_formula = *)
(*     let cache = HAA.create 200001 in *)
(*     fun atoms -> *)
(*       try HAA.find cache atoms *)
(*       with Not_found -> *)
(*         let f = make_neg_formula atoms in *)
(*         HAA.add cache atoms f; *)
(*         f *)


(*   let make_init {t_init = arg, sa } lvars = *)
(*     match arg with *)
(*       | None ->    *)
(* 	  make_formula_set sa *)
(*       | Some z -> *)
(* 	  let sa, cst = SAtom.partition (has_var z) sa in *)
(* 	  let f = make_formula_set cst in *)
(*           List.fold_left (fun acc h -> *)
(*             List.rev_append (make_formula_set (subst_atoms [z, h] sa)) acc) *)
(*             f lvars *)

(*   let mkf f = F.make F.And (List.map (F.make F.Or) f) *)

(**************************************************************)


let unsafe_conj ({ t_unsafe = (args, sa) } as ts) init =
  if debug_smt then eprintf ">>> [smt] safety with: %a@." F.print init;
  SMT.clear ();
  SMT.assume 
    ~profiling ~id:ts.t_nb (distinct_vars (List.length args));
  (* SMT.assume ~profiling ~id:ts.t_nb (order_vars (List.length args)); *)
  if profiling then TimeF.start ();
  let f = make_formula_set sa in
  if profiling then TimeF.pause ();
  if debug_smt then eprintf "[smt] safety: %a and %a@." F.print f F.print init;
  SMT.assume ~profiling ~id:ts.t_nb init;
  SMT.assume ~profiling ~id:ts.t_nb f;
  SMT.check  ~profiling ()

let unsafe_dnf ts dnf =
  try
    let uc =
      List.fold_left (fun accuc init ->
        try 
          unsafe_conj ts init;
          raise Exit
        with Smt.Unsat uc -> List.rev_append uc accuc)
        [] dnf in
    raise (Smt.Unsat uc)
  with Exit -> ()

let unsafe_cdnf ({ t_unsafe = args,_; t_init = i_args, l_inits } as ts) =
  let cdnf_init = make_init_dnfs args in
  List.iter (unsafe_dnf ts) cdnf_init

let unsafe = unsafe_cdnf
  



let reached args s sa =
  SMT.clear ();
  SMT.assume 
    ~profiling ~id:0 (distinct_vars (List.length args));
  (* SMT.assume ~profiling ~id:0 (order_vars (List.length args)); *)
  if profiling then TimeF.start ();
  let f = make_formula_set (SAtom.union sa s) in
  if profiling then TimeF.pause ();
  SMT.assume ~profiling ~id:0 f;
  SMT.check  ~profiling ()


let assume_goal ({t_unsafe = (args, _); t_arru = ap } as ts) =
  SMT.clear ();
  SMT.assume 
    ~profiling ~id:ts.t_nb (distinct_vars (List.length args));
  (* SMT.assume ~profiling ~id:ts.t_nb (order_vars (List.length args)); *)
  if profiling then TimeF.start ();
  let f = make_formula ap in
  if profiling then TimeF.pause ();
  if debug_smt then eprintf "[smt] goal g: %a@." F.print f;
  SMT.assume ~profiling ~id:ts.t_nb f;
  SMT.check  ~profiling ()

let assume_node ap ~id =
  if profiling then TimeF.start ();
  let f = F.make F.Not [make_formula ap] in
  if profiling then TimeF.pause ();
  if debug_smt then eprintf "[smt] assume node: %a@." F.print f;
  SMT.assume ~profiling ~id f;
  SMT.check  ~profiling ()

let run () = SMT.check ~profiling ()

let check_guard args sa reqs =
  SMT.clear ();
  SMT.assume ~profiling ~id:0 (distinct_vars (List.length args));
  if profiling then TimeF.start ();
  let f = make_formula_set (SAtom.union sa reqs) in
  if profiling then TimeF.pause ();
  SMT.assume ~profiling ~id:0 f;
  SMT.check ~profiling ()

let unsat_core_wrt_node uc ap =
  Array.fold_left (fun acc a ->
    match make_literal a with
      | F.Lit la when List.mem [la] uc -> SAtom.add a acc
      | _ -> acc) 
    SAtom.empty ap
  
(*
let extract_candidates args ap forward_nodes =
  List.fold_left (fun acc fs ->
    try
      let c = 
	List.fold_left (fun acc fp ->
	  SMT.clear ();
	  SMT.assume ~profiling (F.Ground (distinct_vars (List.length args)));
	  if profiling then TimeF.start ();
	  let f = F.Ground (make_conjuct ap fp) in
	  if profiling then TimeF.pause ();
	  try 
	    SMT.assume ~profiling f;
	    SMT.check ~profiling;
	    raise Exit
	  with Smt.Unsat uc ->
	    let c = unsat_core_wrt_node uc ap in
	    SAtom.union c acc
	    (* let acc =  *)
	    (*   if !first then (first := false; c) *)
	    (*   else SAtom.inter c acc in *)
	    (* if SAtom.is_empty acc then raise Exit else acc *)
	) SAtom.empty fs
      in if SAtom.cardinal c > 1 then c :: acc else acc
    with Exit -> acc)
    [] forward_nodes
*)



(**************************************)
(* Using enumerated data types solver *)
(**************************************)

module ESMT = Smt.MakeEnum (struct end)

module Enum = struct

  let all_values ty =
    try
      if Hstring.equal ty Smt.Type.type_proc then proc_vars
      else Smt.Type.constructors ty
    with Not_found -> assert false

  let type_of_term = function
    | Elem (x, _) | Access (x, _) -> snd (Smt.Symbol.type_of x)
    | _ -> assert false

  let val_and_mask v ty =
    let mask, va, _ =
      List.fold_left (fun (mask, va, n) c -> 
        (1 lsl n) lor mask,
        (if Hstring.equal v c then (1 lsl n) lor va else va),
        n + 1)
        (0, 0, 0) (all_values ty)
    in va, mask

  let make_eq t v = match t with
    | Elem (x, Glob) ->
        let ty = snd (Smt.Symbol.type_of x) in
        let va, mask = val_and_mask v ty in
        x, va, mask
    | Access (a, lx) ->
        let ty = snd (Smt.Symbol.type_of a) in
        let va, mask = val_and_mask v ty in
        let s = 
          List.fold_left (fun acc x -> acc^(Hstring.view x)) (Hstring.view a) lx
        in
        Hstring.make s, va, mask
    | _ -> assert false


  let neg_lit (h, va, mask) = h, mask land (lnot va), mask
    
  let make_neq t v = neg_lit (make_eq t v)    

  let make_dnf_literal = function
    | True -> [[Hstring.empty, 1, 1]]
    | False -> [[Hstring.empty, 0, 1]]

    | Comp (Elem (x, (Constr|Var)), Eq, Elem (y, (Constr|Var))) ->
        if Hstring.equal x y then [[Hstring.empty, 1, 1]]
        else [[Hstring.empty, 0, 1]]

    | Comp (Elem (x, (Constr|Var)), Neq, Elem (y, (Constr|Var))) ->
        if Hstring.equal x y then [[Hstring.empty, 0, 1]]
        else [[Hstring.empty, 1, 1]]
          
    | Comp (t, Eq, Elem (v, (Constr|Var)))
    | Comp (Elem (v, (Constr|Var)), Eq, t) ->
        [[make_eq t v]]
          
    | Comp (t, Neq, Elem (v, (Constr|Var)))
    | Comp (Elem (v, (Constr|Var)), Neq, t) ->
        [[make_neq t v]]

    | Comp (x, Eq, y) ->
        let vs_x = all_values (type_of_term x) in
        let vs_y = all_values (type_of_term y) in
        List.fold_left (fun acc vx ->
          if Hstring.list_mem vx vs_y then
            [make_eq x vx; make_eq y vx] :: acc
          else acc) [] vs_x
          
    | Comp (x, Neq, y) ->
        let vs_x = all_values (type_of_term x) in
        let vs_y = all_values (type_of_term y) in
        List.fold_left (fun acc vx ->
          if Hstring.list_mem vx vs_y then
            [make_eq x vx; make_neq y vx] :: acc
          else [make_eq x vx] :: acc) [] vs_x
          
    | _ -> assert false

  let make_literal a =
    List.rev_map (List.rev_map neg_lit) (make_dnf_literal (neg a))        

  let make_formula atoms =
    Array.fold_left (fun acc a ->
      List.rev_append (make_literal a) acc)
      [] atoms

  (* let make_formula = *)
  (*   let cache = HAA.create 200001 in *)
  (*   fun atoms -> *)
  (*     try HAA.find cache atoms *)
  (*     with Not_found -> *)
  (*       let f = make_formula atoms in *)
  (*       HAA.add cache atoms f; *)
  (*       f *)

  let make_formula_set atoms =
    SAtom.fold (fun a acc -> List.rev_append (make_literal a) acc) atoms []

  let make_neg_formula atoms =
    let res = 
    Array.fold_left (fun acc a ->
      List.fold_left (fun acc' l -> 
        List.rev_append (List.rev_map (fun d -> l @ d) acc) acc')
        [] (make_literal (neg a)))
      [[]] atoms
    in
    (* if List.length res > 1 then begin *)
    (*   eprintf "make neg of %a =@." Pretty.print_array atoms; *)
    (*   List.iter (fun d -> *)
    (*     eprintf "[ "; *)
    (*     List.iter (fun (x,v,_) -> eprintf "%a = %d , " Hstring.print x v) d; *)
    (*     eprintf "]@."; *)
    (*   ) res; *)
    (*   eprintf "@."; *)
    (* end; *)
    res
    

  let make_neg_formula =
    let cache = HAA.create 200001 in
    fun atoms ->
      try HAA.find cache atoms
      with Not_found ->
        let f = make_neg_formula atoms in
        HAA.add cache atoms f;
        f

  let make_init {t_init = arg, sa } lvars = assert false
    (* match arg with *)
    (*   | None ->    *)
    (*       make_formula_set sa *)
    (*   | Some z -> *)
    (*       let sa, cst = SAtom.partition (has_var z) sa in *)
    (*       let f = make_formula_set cst in *)
    (*       List.fold_left (fun acc h -> *)
    (*         List.rev_append (make_formula_set (subst_atoms [z, h] sa)) acc) *)
    (*         f lvars *)

  let unsafe ({ t_unsafe = (args, sa) } as ts) =
    ESMT.clear ();
    if profiling then TimeF.start ();
    let init = make_init ts (* (List.rev_append ts.t_glob_proc  *) args in
    let f = make_formula_set sa in
    if profiling then TimeF.pause ();
    (* if debug_smt then eprintf "[smt] safety: %a and %a@." F.print f F.print init; *)
    ESMT.assume ~profiling ~id:ts.t_nb init;
    ESMT.assume ~profiling ~id:ts.t_nb f;
    ESMT.check  ~profiling ()


  let assume_goal ({t_unsafe = (args, _); t_arru = ap } as ts) =
    ESMT.clear ();
    if profiling then TimeF.start ();
    let f = make_formula ap in
    if profiling then TimeF.pause ();
    (* if debug_smt then eprintf "[smt] goal g: %a@." F.print f; *)
    ESMT.assume ~profiling ~id:ts.t_nb f;
    ESMT.check  ~profiling ()

  let assume_node ap ~id =
    if profiling then TimeF.start ();
    let f = make_neg_formula ap in
    if profiling then TimeF.pause ();
    (* if debug_smt then eprintf "[smt] assume node: %a@." F.print f; *)
    ESMT.assume ~profiling ~id f;
    ESMT.check  ~profiling ()

end



let unsafe s = if Options.enumsolver then Enum.unsafe s else unsafe s

let assume_goal s = 
  if Options.enumsolver then Enum.assume_goal s else assume_goal s

let assume_node ap ~id =
  if Options.enumsolver then Enum.assume_node ap ~id else assume_node ap ~id


(* let assume_goal s = *)
(*   let res = try assume_goal s; false with Smt.Unsat _ -> true in *)
(*   let eres = try Enum.assume_goal s; false with Smt.Unsat _ -> true in *)
(*   if res <> eres then assert false; *)
(*   if res then raise (Smt.Unsat []) *)
(*   (\* if Options.enumsolver then Enum.assume_goal s else assume_goal s *\) *)

(* let assume_node ap ~id = *)
(*   let res = try assume_node ap ~id; false with Smt.Unsat _ -> true in *)
(*   let eres =try Enum.assume_node ap ~id; false with Smt.Unsat _ -> true in *)
(*   if res <> eres then (printf "smt : %b - enum %b@." res eres; assert false); *)
(*   if res then raise (Smt.Unsat []) *)
(*   (\* if Options.enumsolver then Enum.assume_node ap ~id else assume_node ap ~id *\) *)
