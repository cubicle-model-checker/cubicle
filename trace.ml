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

module HSet = Hstring.HSet

module type S = sig
    val certificate : t_system list -> t_system list -> unit
end


let collect_types s =
  let add = List.fold_left (fun acc g ->
			    let t_args, t_ret = Smt.Symbol.type_of g in
			    List.fold_left (fun acc t -> HSet.add t acc)
					   (HSet.add t_ret acc) t_args
			   ) in
  add (add HSet.empty s.t_globals) s.t_arrays

let need_bool s =
  let f = List.fold_left (fun acc t ->
      acc || Hstring.equal Smt.Type.type_bool (snd (Smt.Symbol.type_of t))
    ) in
  f (f false s.t_globals) s.t_arrays

module AltErgo = struct

  let rec print_constructors fmt = function
    | [] -> assert false
    | [c] -> Hstring.print fmt c
    | c :: r -> fprintf fmt "%a | %a" Hstring.print c print_constructors r 

  let print_type_def fmt t =
      match Smt.Type.constructors t with
      | [] -> fprintf fmt "type %a" Hstring.print t
      | cstrs ->
	 fprintf fmt "type %a = %a" Hstring.print t print_constructors cstrs
      

  let add_type_defs fmt s =
    HSet.iter (fun t ->
      if not (Hstring.list_mem t [Smt.Type.type_proc;
				  Smt.Type.type_bool;
				  Smt.Type.type_int;
				  Smt.Type.type_bool]) then 
	       fprintf fmt "%a@." print_type_def t) (collect_types s)


  let print_type fmt t = 
    let t =
      if Hstring.equal t Smt.Type.type_proc then Smt.Type.type_int else t in
    Hstring.print fmt t
    
  let rec print_type_args fmt = function
    | [] -> assert false
    | [t] -> print_type fmt t
    | t :: r -> fprintf fmt "%a, %a" print_type t print_type_args r

  let spr prime = if prime then "'" else ""

  let print_decl ?(prime=false) fmt s =
    let t_args, t_ret = Smt.Symbol.type_of s in
    match t_args with
    | [] -> fprintf fmt "logic %a%s : %a" Hstring.print s 
		     (spr prime) print_type t_ret 
    | _ -> fprintf fmt "logic %a%s : %a -> %a" Hstring.print s 
		   (spr prime) print_type_args t_args
		   print_type t_ret

  let add_decls fmt s =
    let d = List.iter (fprintf fmt "%a@." (print_decl ~prime:false)) in
    let d_prime = List.iter (fprintf fmt "%a@." (print_decl ~prime:true)) in
    d s.t_globals; d_prime s.t_globals;
    d s.t_arrays; d_prime s.t_arrays

  
  let op_comp = function Eq -> "=" | Lt -> "<" | Le -> "<=" | Neq -> "<>"
  let op_arith = function Plus -> "+" | Minus -> "-"

  let print_const fmt c = assert false

  let print_cs fmt cs = assert false

  let print_proc fmt s = 
    try Scanf.sscanf (Hstring.view s) "#%d" (fun id -> fprintf fmt "z%d" id)
    with Scanf.Scan_failure _ -> Hstring.print fmt s

  let rec print_args fmt = function
    | [] -> assert false
    | [p] -> print_proc fmt p
    | p :: r -> fprintf fmt "%a,%a" print_proc p print_args r

  let rec print_term ~prime fmt = function
    | Const cs -> print_cs fmt cs
    | Elem (s, Var) -> print_proc fmt s
    | Elem (s, Constr) when Hstring.equal s hfalse -> fprintf fmt "false"
    | Elem (s, Constr) when Hstring.equal s htrue -> fprintf fmt "true"
    | Elem (s, Constr) -> fprintf fmt "%a" Hstring.print s
    | Elem (s, (Glob | Arr)) -> fprintf fmt "%a%s" Hstring.print s (spr prime) 
    | Access (a, li) ->
       fprintf fmt "%a%s(%a)" Hstring.print a (spr prime) print_args li
    | Arith (x, cs) -> 
       fprintf fmt "@[%a%a@]" (print_term ~prime) x print_cs cs

  let rec print_atom ~prime fmt = function
    | True -> fprintf fmt "true"
    | False -> fprintf fmt "false"
    | Comp (x, op, y) -> 
       fprintf fmt "%a %s %a" 
	       (print_term ~prime) x (op_comp op) (print_term ~prime) y
    | Ite (la, a1, a2) ->
       fprintf fmt "@[(if (%a) then@ %a@ else@ %a)@]" 
	       (print_atoms ~prime "and") (SAtom.elements la) 
	       (print_atom ~prime) a1 (print_atom ~prime) a2

  and print_atoms ~prime sep fmt = function
    | [] -> ()
    | [a] -> print_atom ~prime fmt a
    | a::l -> fprintf fmt "%a %s@\n%a" (print_atom ~prime) a sep
		      (print_atoms ~prime sep) l

  let print_cube ~prime fmt sa = 
    fprintf fmt "%a" (print_atoms ~prime "and") (SAtom.elements sa)

  let print_array ~prime fmt a =
    fprintf fmt "%a" (print_atoms ~prime "and") (Array.to_list a)

  let prod vars =
    let prod, _ = List.fold_left (fun (acc, vars) v -> 
		    match vars with
		    | [] | [_] -> (acc, vars)
		    | _ -> 
		       let vars = List.tl vars in
		       List.fold_left (fun acc v' -> (v, v') :: acc) acc vars,
		       vars
		    )
		   ([], vars) vars in
    prod

  let print_distinct fmt vars = match vars with
    | [] | [_] -> ()
    | _ -> List.iter (fun (v1, v2) ->
		      fprintf fmt "%a <> %a and "  print_proc v1 print_proc v2)
		     (prod vars)

  let print_system ~prime fmt {t_unsafe = args, sa} = 
    begin match args with
	  | [] -> () 
	  | _  -> fprintf fmt "exists %a:int. %a" 
			  print_args args print_distinct args
    end;
    fprintf fmt "%a" (print_cube ~prime) sa

  let print_neg_system ~prime fmt {t_unsafe = args, sa} = 
    begin match args with
	  | [] -> fprintf fmt "not ("
	  | _  -> fprintf fmt "forall %a:int. not (%a" 
			  print_args args print_distinct args
    end;
    fprintf fmt "%a)" (print_cube ~prime) sa

  let rec print_invariant ~prime fmt visited = match visited with
    | [] -> assert false
    | [s] -> fprintf fmt "not (%a)" (print_system ~prime) s
    | s ::r -> fprintf fmt "not (%a) and\n%a"
		       (print_system ~prime) s (print_invariant ~prime) r


  let rec print_invariant_split ~prime fmt =
    let cpt = ref 1 in
    List.iter (fun s ->
	       fprintf fmt "goal invariant_preserved_%d:\nnot (%a)\n@."
		       !cpt (print_system ~prime) s;
	       incr cpt)

  let rec print_disj ~prime fmt lsa = match lsa with
    | [] -> assert false
    | [sa] -> fprintf fmt "(%a)" (print_cube ~prime) sa
    | sa :: l -> fprintf fmt "(%a) or\n%a" (print_cube ~prime) sa
			 (print_disj ~prime) l

  let print_init fmt (args, lsa) =
    begin match args with
	  | [] -> () 
	  | _  -> fprintf fmt "forall %a:int[%a]. "
			  print_args args print_args args
    end;
    print_disj ~prime:false fmt lsa


  let distinct_from_params_imp fmt j args = match args with
    | [] -> ()
    | _ -> List.iter (fun v ->
		      fprintf fmt "%a = %a or "  print_proc v print_proc j)
		     args

  let print_assign fmt (g, t) =
    fprintf fmt "%a' = %a" Hstring.print g (print_term ~prime:false) t

  let rec add_assign_list globals fmt = function
    | [] -> globals
    | [g,t] -> fprintf fmt "%a" print_assign (g,t);
	       HSet.remove g globals
    | (g,t) :: r ->
       fprintf fmt "%a and\n" print_assign (g,t);
       add_assign_list (HSet.remove g globals) fmt r

  let rec print_assigns_unchanged fmt = function
    | [] -> ()
    | [g] -> fprintf fmt "%a' = %a" Hstring.print g Hstring.print g
    | g::r -> fprintf fmt "%a' = %a and\n%a" Hstring.print g Hstring.print g
		      print_assigns_unchanged r


  let print_assigns globals fmt ass =
    let globals = List.fold_left (fun acc g -> HSet.add g acc)
				 HSet.empty globals in
    let remaining = add_assign_list globals fmt ass in
    let remaining = HSet.elements remaining in
    if ass <> [] && remaining <> [] then fprintf fmt " and\n";
    print_assigns_unchanged fmt remaining

  let rec print_ite fmt (a, args, swts, default) =
    match swts with
    | [] -> 
       fprintf fmt "%a'(%a) = %a"
	       Hstring.print a print_args args (print_term ~prime:false) default
    | (cond, t) :: r ->
       fprintf fmt "((%a) -> %a'(%a) = %a) and\n"
	       (print_cube ~prime:false) cond
	       Hstring.print a print_args args (print_term ~prime:false) t;
       fprintf fmt "(not (%a) -> %a)"
	       (print_cube ~prime:false) cond
	       print_ite (a, args, r, default)

  let print_update fmt {up_arr=a; up_arg=args; up_swts=swts} =
    let rec sd acc = function
      | [] -> assert false
      | [d] -> acc, d
      | s::r -> sd (s::acc) r in
    let swts, (_, default) = sd [] swts in
    fprintf fmt "forall %a:int.\n" print_args args;
    print_ite fmt (a, args, swts, default)


  let rec add_updates_list arrays fmt = function
    | [] -> arrays
    | [{up_arr=a} as u] ->
       fprintf fmt "(%a)" print_update u;
       HSet.remove a arrays
    | ({up_arr=a} as u) :: r ->
       fprintf fmt "(%a) and\n" print_update u;
       add_updates_list (HSet.remove a arrays) fmt r


  let print_unchanged fmt a =
    let targs, _ = Smt.Symbol.type_of a in
    let args, _ = 
      List.fold_left (fun (acc, n) _ ->
	Hstring.make ("z"^(string_of_int n)) :: acc, n + 1)
	 ([], 1) targs in
    let args = List.rev args in
    fprintf fmt "forall %a:int. " print_args args;
    fprintf fmt "%a'(%a) = %a(%a)"
	    Hstring.print a print_args args 
	    Hstring.print a print_args args

  let rec print_all_unchanged fmt = function
    | [] -> ()
    | [a] -> fprintf fmt "(%a) " print_unchanged a
    | a::r -> fprintf fmt "(%a) and\n%a"
		      print_unchanged a
		      print_all_unchanged r

  let print_updates arrays fmt upds =
    let arrays = List.fold_left (fun acc a -> Hstring.HSet.add a acc)
				Hstring.HSet.empty arrays in
    let remaining = add_updates_list arrays fmt upds in
    HSet.iter (fprintf fmt "and (%a)\n" print_unchanged) remaining

  let print_updates arrays fmt upds =
    let arrays = List.fold_left (fun acc a -> HSet.add a acc)
				HSet.empty arrays in
    let remaining = add_updates_list arrays fmt upds in
    let remaining = HSet.elements remaining in
    if upds <> [] && remaining <> [] then fprintf fmt " and\n";
    print_all_unchanged fmt remaining


  let rec make_norm_subst acc = function
    | [], _ | _, [] -> List.rev acc
    | a::ar, v::vr -> make_norm_subst ((a, v) :: acc) (ar, vr)

  let max_quant arrays =
    let nb = 
      List.fold_left (fun acc a -> 
        max (List.length (fst (Smt.Symbol.type_of a))) acc) 0 arrays in
    let rec zify acc = function 
      | 0 -> acc 
      | n ->
	 let z = Hstring.make ("z"^(string_of_int n)) in
	 zify (z :: acc) (n - 1) in
    zify [] nb

  let print_norm_update vars fmt {up_arr=a; up_arg=args; up_swts=swts} =
    let sigma = make_norm_subst [] (args, vars) in
    let args = List.map snd sigma in
    let swts = List.map (fun (cond, t) ->
			 subst_atoms sigma cond, subst_term sigma t) swts in
    let rec sd acc = function
      | [] -> assert false
      | [d] -> acc, d
      | s::r -> sd (s::acc) r in
    let swts, (_, default) = sd [] swts in
    print_ite fmt (a, args, swts, default)

  let rec add_norm_updates vars arrays fmt = function
    | [] -> arrays
    | [{up_arr=a} as u] ->
       fprintf fmt "(%a)" (print_norm_update vars) u;
       HSet.remove a arrays
    | ({up_arr=a} as u) :: r ->
       fprintf fmt "(%a) and\n" (print_norm_update vars) u;
       add_norm_updates vars (HSet.remove a arrays) fmt r

  let print_norm_unchanged vars fmt a =
    let targs, _ = Smt.Symbol.type_of a in
    let rec select_vars acc = function
      | [], _ | _, [] -> List.rev acc
      | t::tr, v::vr -> select_vars (v::acc) (tr, vr) in
    let args = select_vars [] (targs, vars) in
    fprintf fmt "%a'(%a) = %a(%a)"
	    Hstring.print a print_args args 
	    Hstring.print a print_args args

  let rec print_norm_all_unchanged vars fmt = function
    | [] -> ()
    | [a] -> fprintf fmt "(%a) " (print_norm_unchanged vars) a
    | a::r -> fprintf fmt "(%a) and\n%a"
		      (print_norm_unchanged vars) a
		      (print_norm_all_unchanged vars) r

  let print_norm_updates arrays fmt upds =
    let vars = max_quant arrays in
    let arrays = List.fold_left (fun acc a -> HSet.add a acc)
				HSet.empty arrays in
    fprintf fmt "forall %a:int.\n" print_args vars;
    let remaining = add_norm_updates vars arrays fmt upds in
    let remaining = HSet.elements remaining in
    if upds <> [] && remaining <> [] then fprintf fmt " and\n";
    print_norm_all_unchanged vars fmt remaining

  let print_transtion s fmt t =
    fprintf fmt "(* transition %a *)\n" Hstring.print t.tr_name;
    fprintf fmt "(";
    let args =  t.tr_args in
    begin match args with
	  | [] -> ()
	  | _  -> fprintf fmt "exists %a:int. %a\n" 
			  print_args args print_distinct args
    end;
    fprintf fmt "( (* requires *)\n";
    print_cube ~prime:false fmt t.tr_reqs;
    List.iter (fun (j, disj) ->
      fprintf fmt "\nand (forall %a:int." print_proc j;
      distinct_from_params_imp fmt j args;
      fprintf fmt "\n%a" (print_disj ~prime:false) disj;
      fprintf fmt ")\n";
    ) t.tr_ureq;
    fprintf fmt ")";
    if s.t_globals <> [] || s.t_arrays <> [] then
      begin
	fprintf fmt " and\n";
	fprintf fmt "( (* actions *)\n";
	print_assigns s.t_globals fmt t.tr_assigns;
	if s.t_globals <> [] && s.t_arrays <> [] then fprintf fmt " and\n";
	(* print_norm_updates s.t_arrays fmt t.tr_upds; *)
	print_updates s.t_arrays fmt t.tr_upds;
	fprintf fmt ")";
      end;
    fprintf fmt ")@."


  let rec print_transitions_disj s fmt = function
    | [] -> ()
    | [t] -> print_transtion s fmt t
    | t :: r -> fprintf fmt "%a\n@.or\n\n%a"
			(print_transtion s) t 
			(print_transitions_disj s) r

  let transition_relation fmt s =
    fprintf fmt "( (* Transition Relation *)@.";
    print_transitions_disj s fmt s.t_trans;
    fprintf fmt ")@."

  let goal_init fmt s visited =
    fprintf fmt "goal initialisation:@.";
    fprintf fmt "(* init *)\n(%a)\n\n->\n\n" print_init s.t_init;
    fprintf fmt "(* invariant *)\n(%a)@." (print_invariant ~prime:false) visited


  let goal_inductive fmt s visited =
    fprintf fmt "goal inductive:@.";
    fprintf fmt "((* invariant before *)\n(%a)@."
	    (print_invariant ~prime:false) visited;
    fprintf fmt "\nand\n%a)@." transition_relation s;
    fprintf fmt "\n->\n\n(* invariant after *)\n(%a)@."
	    (print_invariant ~prime:true) visited

  let goal_inductive_split fmt s visited =
    fprintf fmt "axiom induction_hypothesis:@.";
    fprintf fmt "(* invariant before *)\n(%a)@."
	    (print_invariant ~prime:false) visited;
    fprintf fmt "\n\naxiom transition_relation:@.";
    fprintf fmt "%a@." transition_relation s;
    fprintf fmt "\n(* invariant after *)\n%a@."
	    (print_invariant_split ~prime:true) visited
    

  let goal_property fmt uns visited =
    fprintf fmt "goal property:@.";
    fprintf fmt "(* invariant *)\n(%a)@."
	    (print_invariant ~prime:false) visited;
    fprintf fmt "\n->\n\n(* property *)\n(%a)@."
	    (print_invariant ~prime:false) uns

  let out_dir = ref ""

  let base file = Filename.chop_extension (Filename.basename file)

  let create_dir () =
    let bench = base file in
    let dir = out_trace^"/"^bench^"_certif_altergo" in
    begin 
      try if not (Sys.is_directory dir) then failwith (dir^" is not a directory")
      with Sys_error _ -> Unix.mkdir dir 0o755
    end;
    out_dir := dir

  let add_definitions fmt s =
    add_type_defs fmt s;
    fprintf fmt "@.";
    add_decls fmt s;
    fprintf fmt "@."

  let assume_invariant ~prime fmt visited =
    let cpt = ref 0 in
    List.iter (fun s ->
	       incr cpt;
	       fprintf fmt "axiom induction_hypothesis_%d:\n" !cpt;
	       fprintf fmt "    @[not (%a)@]\n@." (print_system ~prime) s;
	       (* fprintf fmt "    @[%a@]\n@." (print_neg_system ~prime) s; *)
	      ) visited

  let goal_invariant ~prime fmt visited =
    let cpt = ref 0 in
    List.iter (fun s ->
	       incr cpt;
	       fprintf fmt "goal invariant_%d:\n" !cpt;
	       fprintf fmt "    @[not (%a)@]\n@." (print_system ~prime) s;
	       (* fprintf fmt "    @[%a@]\n@." (print_neg_system ~prime) s; *)
	      ) visited    

  let create_init s visited =
    let bench = base file in
    let init_file = !out_dir ^"/"^bench^"_init.why" in
    let cout = open_out init_file in
    let fmt = formatter_of_out_channel cout in
    add_definitions fmt s;
    fprintf fmt "axiom initial:\n%a\n@." print_init s.t_init;
    goal_invariant ~prime:false fmt visited;    
    flush cout; close_out cout

  let create_property s uns visited =
    let bench = base file in
    let init_file = !out_dir ^"/"^bench^"_property.why" in
    let cout = open_out init_file in
    let fmt = formatter_of_out_channel cout in
    add_definitions fmt s;
    assume_invariant ~prime:false fmt visited;
    goal_invariant ~prime:false fmt uns;    
    flush cout; close_out cout

  let create_inductive s visited =
    let bench = base file in
    let init_file = !out_dir ^"/"^bench^"_inductive.why" in
    let cout = open_out init_file in
    let fmt = formatter_of_out_channel cout in
    add_definitions fmt s;
    assume_invariant ~prime:false fmt visited;
    fprintf fmt "\naxiom transition_relation:@.";
    fprintf fmt "%a\n@." transition_relation s;
    goal_invariant ~prime:true fmt visited;
    flush cout; close_out cout

  let certificate uns visited =
    let s = List.hd uns in
    create_dir ();
    create_init s visited;
    create_property s uns visited;
    create_inductive s visited;
    printf "Alt-Ergo certificates created in %s@." !out_dir

end


module Why3 = struct

  let print_name fmt s = fprintf fmt "%s" (String.uncapitalize (Hstring.view s))

  let rec print_constructors fmt = function
    | [] -> assert false
    | [c] -> Hstring.print fmt c
    | c :: r -> fprintf fmt "%a | %a" Hstring.print c print_constructors r 

  let print_type_def fmt t =
      match Smt.Type.constructors t with
      | [] -> fprintf fmt "type %a" Hstring.print t
      | cstrs ->
	 fprintf fmt "type %a = %a" Hstring.print t print_constructors cstrs
      

  let add_type_defs fmt s =
    HSet.iter (fun t ->
      if not (Hstring.list_mem t [Smt.Type.type_proc;
				  Smt.Type.type_bool;
				  Smt.Type.type_int;
				  Smt.Type.type_bool]) then 
	       fprintf fmt "%a@." print_type_def t) (collect_types s)


  let print_type fmt t = 
    let t =
      if Hstring.equal t Smt.Type.type_proc then Smt.Type.type_int else t in
    Hstring.print fmt t
    
  let rec print_type_args fmt = function
    | [] -> assert false
    | [t] -> print_type fmt t
    | t :: r -> fprintf fmt "%a, %a" print_type t print_type_args r

  let spr prime = if prime then "'" else ""

  let print_decl ?(prime=false) fmt s =
    let t_args, t_ret = Smt.Symbol.type_of s in
    fprintf fmt "function %a%s " print_name s (spr prime);
    List.iter (fprintf fmt "%a " print_type) t_args;
    fprintf fmt ": %a" print_type t_ret

  let add_decls fmt s =
    let d = List.iter (fprintf fmt "%a@." (print_decl ~prime:false)) in
    let d_prime = List.iter (fprintf fmt "%a@." (print_decl ~prime:true)) in
    d s.t_globals; d_prime s.t_globals;
    d s.t_arrays; d_prime s.t_arrays

  
  let op_comp = function Eq -> "=" | Lt -> "<" | Le -> "<=" | Neq -> "<>"
  let op_arith = function Plus -> "+" | Minus -> "-"

  let print_const fmt c = assert false

  let print_cs fmt cs = assert false

  let print_proc fmt s = 
    try Scanf.sscanf (Hstring.view s) "#%d" (fun id -> fprintf fmt "z%d" id)
    with Scanf.Scan_failure _ -> print_name fmt s

  let rec print_args fmt = function
    | [] -> assert false
    | [p] -> print_proc fmt p
    | p :: r -> fprintf fmt "%a %a" print_proc p print_args r

  let rec print_term ~prime fmt = function
    | Const cs -> print_cs fmt cs
    | Elem (s, Var) -> print_proc fmt s
    | Elem (s, Constr) -> fprintf fmt "%a" Hstring.print s
    | Elem (s, (Glob | Arr)) -> fprintf fmt "%a%s" print_name s (spr prime) 
    | Access (a, li) ->
       fprintf fmt "(%a%s %a)" print_name a (spr prime) print_args li
    | Arith (x, cs) -> 
       fprintf fmt "@[(%a%a)@]" (print_term ~prime) x print_cs cs

  let rec print_atom ~prime fmt = function
    | True -> fprintf fmt "true"
    | False -> fprintf fmt "false"
    | Comp (x, op, y) -> 
       fprintf fmt "%a %s %a" 
	       (print_term ~prime) x (op_comp op) (print_term ~prime) y
    | Ite (la, a1, a2) ->
       fprintf fmt "@[(if %a then@ %a@ else@ %a)@]" 
	       (print_atoms ~prime "/\\") (SAtom.elements la) 
	       (print_atom ~prime) a1 (print_atom ~prime) a2

  and print_atoms ~prime sep fmt = function
    | [] -> ()
    | [a] -> print_atom ~prime fmt a
    | a::l -> fprintf fmt "%a %s@\n%a" (print_atom ~prime) a sep
		      (print_atoms ~prime sep) l

  let print_cube ~prime fmt sa = 
    fprintf fmt "%a" (print_atoms ~prime "/\\") (SAtom.elements sa)

  let print_array ~prime fmt a =
    fprintf fmt "%a" (print_atoms ~prime "/\\") (Array.to_list a)

  let prod vars =
    let prod, _ = List.fold_left (fun (acc, vars) v -> 
		    match vars with
		    | [] | [_] -> (acc, vars)
		    | _ -> 
		       let vars = List.tl vars in
		       List.fold_left (fun acc v' -> (v, v') :: acc) acc vars,
		       vars
		    )
		   ([], vars) vars in
    prod

  let print_distinct fmt vars = match vars with
    | [] | [_] -> ()
    | _ -> List.iter (fun (v1, v2) ->
		      fprintf fmt "%a <> %a /\\ "  print_proc v1 print_proc v2)
		     (prod vars)

  let print_system ~prime fmt {t_unsafe = args, sa} = 
    begin match args with
	  | [] -> () 
	  | _  -> fprintf fmt "exists %a:int. %a" 
			  print_args args print_distinct args
    end;
    fprintf fmt "%a" (print_cube ~prime) sa

  let rec print_invariant ~prime fmt visited = match visited with
    | [] -> assert false
    | [s] -> fprintf fmt "not (%a)" (print_system ~prime) s
    | s ::r -> fprintf fmt "not (%a) /\\\n%a"
		       (print_system ~prime) s (print_invariant ~prime) r


  let rec print_invariant_split ~prime fmt =
    let cpt = ref 1 in
    List.iter (fun s ->
	       fprintf fmt "goal invariant_preserved_%d:\nnot (%a)\n@."
		       !cpt (print_system ~prime) s;
	       incr cpt)

  let rec print_disj ~prime fmt lsa = match lsa with
    | [] -> assert false
    | [sa] -> fprintf fmt "(%a)" (print_cube ~prime) sa
    | sa :: l -> fprintf fmt "(%a) \\/\n%a" (print_cube ~prime) sa
			 (print_disj ~prime) l

  let print_init fmt (args, lsa) =
    begin match args with
	  | [] -> () 
	  | _  -> fprintf fmt "forall %a:int. " print_args args
    end;
    print_disj ~prime:false fmt lsa


  let distinct_from_params_imp fmt j args = match args with
    | [] -> ()
    | _ -> List.iter (fun v ->
		      fprintf fmt "%a = %a \\/ "  print_proc v print_proc j)
		     args

  let print_assign fmt (g, t) =
    fprintf fmt "%a' = %a" print_name g (print_term ~prime:false) t

  let rec add_assign_list globals fmt = function
    | [] -> globals
    | [g,t] -> fprintf fmt "%a" print_assign (g,t);
	       HSet.remove g globals
    | (g,t) :: r ->
       fprintf fmt "%a /\\\n" print_assign (g,t);
       add_assign_list (HSet.remove g globals) fmt r

  let rec print_assigns_unchanged fmt = function
    | [] -> ()
    | [g] -> fprintf fmt "%a' = %a" print_name g print_name g
    | g::r -> fprintf fmt "%a' = %a /\\\n%a" print_name g print_name g
		      print_assigns_unchanged r


  let print_assigns globals fmt ass =
    let globals = List.fold_left (fun acc g -> HSet.add g acc)
				 HSet.empty globals in
    let remaining = add_assign_list globals fmt ass in
    let remaining = HSet.elements remaining in
    if ass <> [] && remaining <> [] then fprintf fmt " /\\\n";
    print_assigns_unchanged fmt remaining

  let rec print_ite fmt (a, args, swts, default) =
    match swts with
    | [] -> 
       fprintf fmt "%a' %a = %a"
	       print_name a print_args args (print_term ~prime:false) default
    | (cond, t) :: r ->
       fprintf fmt "if %a then\n %a' %a = %a\nelse %a"
	       (print_cube ~prime:false) cond
	       print_name a print_args args (print_term ~prime:false) t
	       print_ite (a, args, r, default)

  let print_update fmt {up_arr=a; up_arg=args; up_swts=swts} =
    let rec sd acc = function
      | [] -> assert false
      | [d] -> acc, d
      | s::r -> sd (s::acc) r in
    let swts, (_, default) = sd [] swts in
    fprintf fmt "forall %a:int.\n" print_args args;
    print_ite fmt (a, args, swts, default)


  let rec add_updates_list arrays fmt = function
    | [] -> arrays
    | [{up_arr=a} as u] ->
       fprintf fmt "(%a)" print_update u;
       HSet.remove a arrays
    | ({up_arr=a} as u) :: r ->
       fprintf fmt "(%a) /\\\n" print_update u;
       add_updates_list (HSet.remove a arrays) fmt r


  let print_unchanged fmt a =
    let targs, _ = Smt.Symbol.type_of a in
    let args, _ = 
      List.fold_left (fun (acc, n) _ ->
	Hstring.make ("z"^(string_of_int n)) :: acc, n + 1)
	 ([], 1) targs in
    let args = List.rev args in
    fprintf fmt "forall %a:int. " print_args args;
    fprintf fmt "%a' %a = %a %a"
	    print_name a print_args args 
	    print_name a print_args args

  let rec print_all_unchanged fmt = function
    | [] -> ()
    | [a] -> fprintf fmt "(%a) " print_unchanged a
    | a::r -> fprintf fmt "(%a) /\\\n%a"
		      print_unchanged a
		      print_all_unchanged r

  let print_updates arrays fmt upds =
    let arrays = List.fold_left (fun acc a -> Hstring.HSet.add a acc)
				Hstring.HSet.empty arrays in
    let remaining = add_updates_list arrays fmt upds in
    HSet.iter (fprintf fmt "/\\ (%a)\n" print_unchanged) remaining

  let print_updates arrays fmt upds =
    let arrays = List.fold_left (fun acc a -> HSet.add a acc)
				HSet.empty arrays in
    let remaining = add_updates_list arrays fmt upds in
    let remaining = HSet.elements remaining in
    if upds <> [] && remaining <> [] then fprintf fmt " /\\\n";
    print_all_unchanged fmt remaining


  let rec make_norm_subst acc = function
    | [], _ | _, [] -> List.rev acc
    | a::ar, v::vr -> make_norm_subst ((a, v) :: acc) (ar, vr)

  let max_quant arrays =
    let nb = 
      List.fold_left (fun acc a -> 
        max (List.length (fst (Smt.Symbol.type_of a))) acc) 0 arrays in
    let rec zify acc = function 
      | 0 -> acc 
      | n ->
	 let z = Hstring.make ("z"^(string_of_int n)) in
	 zify (z :: acc) (n - 1) in
    zify [] nb

  let print_norm_update vars fmt {up_arr=a; up_arg=args; up_swts=swts} =
    let sigma = make_norm_subst [] (args, vars) in
    let args = List.map snd sigma in
    let swts = List.map (fun (cond, t) ->
			 subst_atoms sigma cond, subst_term sigma t) swts in
    let rec sd acc = function
      | [] -> assert false
      | [d] -> acc, d
      | s::r -> sd (s::acc) r in
    let swts, (_, default) = sd [] swts in
    print_ite fmt (a, args, swts, default)

  let rec add_norm_updates vars arrays fmt = function
    | [] -> arrays
    | [{up_arr=a} as u] ->
       fprintf fmt "(%a)" (print_norm_update vars) u;
       HSet.remove a arrays
    | ({up_arr=a} as u) :: r ->
       fprintf fmt "(%a) /\\\n" (print_norm_update vars) u;
       add_norm_updates vars (HSet.remove a arrays) fmt r

  let print_norm_unchanged vars fmt a =
    let targs, _ = Smt.Symbol.type_of a in
    let rec select_vars acc = function
      | [], _ | _, [] -> List.rev acc
      | t::tr, v::vr -> select_vars (v::acc) (tr, vr) in
    let args = select_vars [] (targs, vars) in
    fprintf fmt "%a' %a = %a %a"
	    print_name a print_args args 
	    print_name a print_args args

  let rec print_norm_all_unchanged vars fmt = function
    | [] -> ()
    | [a] -> fprintf fmt "(%a) " (print_norm_unchanged vars) a
    | a::r -> fprintf fmt "(%a) /\\\n%a"
		      (print_norm_unchanged vars) a
		      (print_norm_all_unchanged vars) r

  let print_norm_updates arrays fmt upds =
    let vars = max_quant arrays in
    let arrays = List.fold_left (fun acc a -> HSet.add a acc)
				HSet.empty arrays in
    fprintf fmt "forall %a:int.\n" print_args vars;
    let remaining = add_norm_updates vars arrays fmt upds in
    let remaining = HSet.elements remaining in
    if upds <> [] && remaining <> [] then fprintf fmt " /\\\n";
    print_norm_all_unchanged vars fmt remaining

  let print_transtion s fmt t =
    fprintf fmt "(* transition %a *)\n" Hstring.print t.tr_name;
    fprintf fmt "(";
    let args =  t.tr_args in
    begin match args with
	  | [] -> ()
	  | _  -> fprintf fmt "exists %a:int. %a\n" 
			  print_args args print_distinct args
    end;
    fprintf fmt "( (* requires *)\n";
    print_cube ~prime:false fmt t.tr_reqs;
    List.iter (fun (j, disj) ->
      fprintf fmt "\n/\\ (forall %a:int." print_proc j;
      distinct_from_params_imp fmt j args;
      fprintf fmt "\n%a" (print_disj ~prime:false) disj;
      fprintf fmt ")\n";
    ) t.tr_ureq;
    fprintf fmt ")";
    if s.t_globals <> [] || s.t_arrays <> [] then
      begin
	fprintf fmt " /\\\n";
	fprintf fmt "( (* actions *)\n";
	print_assigns s.t_globals fmt t.tr_assigns;
	if s.t_globals <> [] && s.t_arrays <> [] then fprintf fmt " /\\\n";
	(* print_norm_updates s.t_arrays fmt t.tr_upds; *)
	print_updates s.t_arrays fmt t.tr_upds;
	fprintf fmt ")";
      end;
    fprintf fmt ")@."


  let rec print_transitions_disj s fmt = function
    | [] -> ()
    | [t] -> print_transtion s fmt t
    | t :: r -> fprintf fmt "%a\n@.\\/\n\n%a"
			(print_transtion s) t 
			(print_transitions_disj s) r

  let transition_relation fmt s =
    fprintf fmt "( (* Transition Relation *)@.";
    print_transitions_disj s fmt s.t_trans;
    fprintf fmt ")@."

  let goal_init fmt s visited =
    fprintf fmt "goal initialisation:@.";
    fprintf fmt "(* init *)\n(%a)\n\n->\n\n" print_init s.t_init;
    fprintf fmt "(* invariant *)\n(%a)@." (print_invariant ~prime:false) visited


  let goal_inductive fmt s visited =
    fprintf fmt "goal inductive:@.";
    fprintf fmt "((* invariant before *)\n(%a)@."
	    (print_invariant ~prime:false) visited;
    fprintf fmt "\n/\\\n%a)@." transition_relation s;
    fprintf fmt "\n->\n\n(* invariant after *)\n(%a)@."
	    (print_invariant ~prime:true) visited

  let goal_inductive_split fmt s visited =
    fprintf fmt "axiom induction_hypothesis:@.";
    fprintf fmt "(* invariant before *)\n(%a)@."
	    (print_invariant ~prime:false) visited;
    fprintf fmt "\n\naxiom transition_relation:@.";
    fprintf fmt "%a@." transition_relation s;
    fprintf fmt "\n(* invariant after *)\n%a@."
	    (print_invariant_split ~prime:true) visited
    

  let goal_property fmt uns visited =
    fprintf fmt "goal property:@.";
    fprintf fmt "(* invariant *)\n(%a)@."
	    (print_invariant ~prime:false) visited;
    fprintf fmt "\n->\n\n(* property *)\n(%a)@."
	    (print_invariant ~prime:false) uns

  let assume_invariant ~prime fmt visited =
    let cpt = ref 0 in
    List.iter (fun s ->
	       incr cpt;
	       fprintf fmt "axiom induction_hypothesis_%d:\n" !cpt;
	       fprintf fmt "    @[not (%a)@]\n@." (print_system ~prime) s;
	      ) visited

  let goal_invariant ~prime fmt visited =
    let cpt = ref 0 in
    List.iter (fun s ->
	       incr cpt;
	       fprintf fmt "goal invariant_%d:\n" !cpt;
	       fprintf fmt "    @[not (%a)@]\n@." (print_system ~prime) s;
	      ) visited    

  let add_imports fmt s l =
    if need_bool s then fprintf fmt "use import bool.Bool\n";
    List.iter (fprintf fmt "use import %s\n") l;
    fprintf fmt "@."


  let capital_base f =
    String.capitalize (Filename.chop_extension (Filename.basename f))

  let theory_defs fmt s =
    let name = (capital_base file)^"_defs" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s [];
    add_type_defs fmt s;
    fprintf fmt "@.";
    add_decls fmt s;    
    fprintf fmt "\nend\n\n@.";
    name

  let theory_init fmt s visited imports =
    let name = (capital_base file)^"_initialisation" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    fprintf fmt "axiom initial:\n%a\n@." print_init s.t_init;
    goal_invariant ~prime:false fmt visited;
    fprintf fmt "\nend\n\n@."
    
  let theory_property fmt s uns visited imports =
    let name = (capital_base file)^"_property" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    assume_invariant ~prime:false fmt visited;
    goal_invariant ~prime:false fmt uns;
    fprintf fmt "\nend\n\n@."

  let theory_preservation fmt s visited imports =
    let name = (capital_base file)^"_preservation" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    assume_invariant ~prime:false fmt visited;
    fprintf fmt "\naxiom transition_relation:@.";
    fprintf fmt "%a\n@." transition_relation s;
    goal_invariant ~prime:true fmt visited;
    fprintf fmt "\nend\n\n@."
    
    

  let certificate uns visited =
    let bench = Filename.chop_extension (Filename.basename file) in
    let why_certif = out_trace^"/"^bench^"_certif.why" in
    let cout = open_out why_certif in
    let fmt = formatter_of_out_channel cout in
    let s = List.hd uns in
    let defs = theory_defs fmt s in
    theory_init fmt s visited [defs];
    theory_property fmt s uns visited [defs];
    theory_preservation fmt s visited [defs];
    flush cout; close_out cout;
    printf "Why3 certificate created in %s@." why_certif

end
