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
open Ast
open Cubtypes
open Options

module HSet = Hstring.HSet

module type S = sig
    val certificate : t_system -> Node.t list -> unit
end


(* TODO : Add user invariants as axioms *)

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

let need_real s =
  let f = List.fold_left (fun acc t ->
      acc || Hstring.equal Smt.Type.type_real (snd (Smt.Symbol.type_of t))
    ) in
  f (f false s.t_globals) s.t_arrays


let cert_file_name () =
  let bench = Filename.chop_extension (Filename.basename file) in
  out_trace^"/"^bench^"_certif.why"

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
    | Term.Const cs -> print_cs fmt cs
    | Term.Elem (s, Var) -> print_proc fmt s
    | Term.Elem (s, Constr) when Hstring.equal s Term.hfalse -> fprintf fmt "false"
    | Term.Elem (s, Constr) when Hstring.equal s Term.htrue -> fprintf fmt "true"
    | Term.Elem (s, Constr) -> fprintf fmt "%a" Hstring.print s
    | Term.Elem (s, Glob) -> fprintf fmt "%a%s" Hstring.print s (spr prime) 
    | Term.Access (a, li) ->
       fprintf fmt "%a%s(%a)" Hstring.print a (spr prime) print_args li
    | Term.Arith (x, cs) -> 
       fprintf fmt "@[%a%a@]" (print_term ~prime) x print_cs cs

  let rec print_atom ~prime fmt = function
    | Atom.True -> fprintf fmt "true"
    | Atom.False -> fprintf fmt "false"
    | Atom.Comp (x, op, y) -> 
       fprintf fmt "%a %s %a" 
	       (print_term ~prime) x (op_comp op) (print_term ~prime) y
    | Atom.Ite (la, a1, a2) ->
       fprintf fmt "@[(if (%a) then@ %a@ else@ %a)@]" 
	       (print_atoms ~prime "and") (SAtom.elements la) 
	       (print_atom ~prime) a1 (print_atom ~prime) a2

  and print_atoms ~prime sep fmt = function
    | [] -> ()
    | [a] -> print_atom ~prime fmt a
    | a::l -> fprintf fmt "%a %s@\n%a" (print_atom ~prime) a sep
		      (print_atoms ~prime sep) l

  let print_satom ~prime fmt sa = 
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

  let print_node ~prime fmt n = 
    begin match Node.variables n with
	  | [] -> () 
	  | args -> fprintf fmt "exists %a:int. %a" 
			  print_args args print_distinct args
    end;
    fprintf fmt "%a" (print_satom ~prime) (Node.litterals n)

  let print_neg_node ~prime fmt n = 
    begin match Node.variables n  with
	  | [] -> fprintf fmt "not ("
	  | args -> fprintf fmt "forall %a:int. not (%a" 
			  print_args args print_distinct args
    end;
    fprintf fmt "%a)" (print_satom ~prime) (Node.litterals n)

  let rec print_invariant ~prime fmt visited = match visited with
    | [] -> assert false
    | [s] -> fprintf fmt "not (%a)" (print_node ~prime) s
    | s ::r -> fprintf fmt "not (%a) and\n%a"
		       (print_node ~prime) s (print_invariant ~prime) r


  let rec print_invariant_split ~prime fmt =
    let cpt = ref 1 in
    List.iter (fun s ->
	       fprintf fmt "goal invariant_preserved_%d:\nnot (%a)\n@."
		       !cpt (print_node ~prime) s;
	       incr cpt)

  let rec print_disj ~prime fmt lsa = match lsa with
    | [] -> assert false
    | [sa] -> fprintf fmt "(%a)" (print_satom ~prime) sa
    | sa :: l -> fprintf fmt "(%a) or\n%a" (print_satom ~prime) sa
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

  let split_swts_default swts =
    let rec sd acc = function
      | [] -> assert false
      | [d] -> List.rev acc, d
      | s::r -> sd (s::acc) r in
    let swts, (_, default) = sd [] swts in
    swts, default

  let rec print_ite fmt (nt, swts, default) =
    match swts with
    | [] -> 
       fprintf fmt "%a = %a"
               (print_term ~prime:true) nt
	       (print_term ~prime:false) default
    | (cond, t) :: r ->
       fprintf fmt "((%a) -> %a = %a) and\n"
	       (print_satom ~prime:false) cond
	       (print_term ~prime:true) nt
	       (print_term ~prime:false) t;
       fprintf fmt "(not (%a) -> %a)"
	       (print_satom ~prime:false) cond
	       print_ite (nt, r, default)

  let print_assign fmt (g, gu) =
    match gu with
    | UTerm t -> print_ite fmt (Term.Elem(g, Glob), [], t)
    | UCase swts ->
       let swts, default = split_swts_default swts in
       print_ite fmt (Term.Elem(g, Glob), swts, default)
    
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

  let print_update fmt {up_arr=a; up_arg=args; up_swts=swts} =
    let swts, default = split_swts_default swts in
    fprintf fmt "forall %a:int.\n" print_args args;
    print_ite fmt (Term.Access (a, args), swts, default)


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
			 SAtom.subst sigma cond, Term.subst sigma t) swts in
    let swts, default = split_swts_default swts in
    print_ite fmt (Term.Access (a, args), swts, default)

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

  let print_transtion s fmt {tr_info = t} =
    fprintf fmt "(* transition %a *)\n" Hstring.print t.tr_name;
    fprintf fmt "(";
    let args =  t.tr_args in
    begin match args with
	  | [] -> ()
	  | _  -> fprintf fmt "exists %a:int. %a\n" 
			  print_args args print_distinct args
    end;
    fprintf fmt "( (* requires *)\n";
    print_satom ~prime:false fmt t.tr_reqs;
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
	       fprintf fmt "    @[not (%a)@]\n@." (print_node ~prime) s;
	       (* fprintf fmt "    @[%a@]\n@." (print_neg_system ~prime) s; *)
	      ) visited

  let goal_invariant ~prime fmt visited =
    let cpt = ref 0 in
    List.iter (fun s ->
	       incr cpt;
	       fprintf fmt "goal invariant_%d:\n" !cpt;
	       fprintf fmt "    @[not (%a)@]\n@." (print_node ~prime) s;
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
    (* goal_init fmt s visited; *)
    flush cout; close_out cout

  let create_property s visited =
    let bench = base file in
    let init_file = !out_dir ^"/"^bench^"_property.why" in
    let cout = open_out init_file in
    let fmt = formatter_of_out_channel cout in
    add_definitions fmt s;
    assume_invariant ~prime:false fmt visited;
    goal_invariant ~prime:false fmt s.t_unsafe;    
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

  let certificate s visited =
    create_dir ();
    create_init s visited;
    create_property s visited;
    create_inductive s visited;
    printf "Alt-Ergo certificates created in %s@." !out_dir

end



module Why3 = struct
    

  module CompInt = struct type t = int let compare = Pervasives.compare end

  module NodeH = struct
    type t = Node.t
    let compare n1 n2 = Pervasives.compare n1.tag n2.tag
    let equal n1 n2 = n1.tag == n2.tag
    let hash n = n.tag
  end

  module SI = Set.Make(CompInt)
  module MI = Map.Make(CompInt)
  module NodeMap = Map.Make(NodeH)
  module NH = Hashtbl.Make(NodeH)
  module Fixpoint = Fixpoint.FixpointList

  let sanitize_string_for_why3 s =
    String.map (function
      | '-' | '.' -> '_'
      | c -> c
    ) s

  let print_name fmt s =
    fprintf fmt "%s"
            (String.uncapitalize_ascii
               (sanitize_string_for_why3 (Hstring.view s)))

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
                                  Smt.Type.type_real]) then 
	       fprintf fmt "%a@ " print_type_def t) (collect_types s)


  let print_type fmt t = 
    let t =
      if Hstring.equal t Smt.Type.type_proc then Smt.Type.type_int else t in
    Hstring.print fmt t
    
  let rec print_type_args fmt = function
    | [] -> assert false
    | [t] -> print_type fmt t
    | t :: r -> fprintf fmt "%a, %a" print_type t print_type_args r

  let spr prime = if prime then "'" else ""

  let print_decl ?(prime=false) ?(const=false) fmt s =
    let t_args, t_ret = Smt.Symbol.type_of s in
    fprintf fmt "%s %a%s "
      (if const then "constant" else "function")
      print_name s (spr prime);
    List.iter (fprintf fmt "%a " print_type) t_args;
    fprintf fmt ": %a" print_type t_ret

  let add_decls fmt s =
    let d = List.iter
        (fprintf fmt "%a@ " (print_decl ~prime:false ~const:false)) in
    let c = List.iter
        (fprintf fmt "%a@ " (print_decl ~prime:false ~const:true)) in
    let d_prime = List.iter
        (fprintf fmt "%a@ " (print_decl ~prime:true ~const:false)) in
    d s.t_globals; d_prime s.t_globals;
    fprintf fmt "@\n";
    d s.t_arrays; d_prime s.t_arrays;
    fprintf fmt "@\n";
    c s.t_consts

  
  let op_comp = function Eq -> "=" | Lt -> "<" | Le -> "<=" | Neq -> "<>"

  let print_const fmt = function
    | ConstInt n -> fprintf fmt "%s" (Num.string_of_num n)
    | ConstReal n -> fprintf fmt "%F" (Num.float_of_num n)
    | ConstName n -> fprintf fmt "%a" print_name n

  let print_cs ?(arith=false) fmt cs =
    let ls = MConst.fold (fun c i acc -> (c,i) :: acc) cs [] in
    let rec prpr arith first ls = 
      let put_sign = arith || not first in 
      match ls, put_sign with
      | (c, 1) :: rs, false ->
         print_const fmt c;
         prpr arith false rs
      | (c, -1) :: rs, _ ->
         fprintf fmt " - %a" print_const c;
         prpr arith false rs
      | (c, i) :: rs, false ->
         fprintf fmt "%d * %a" i print_const c;
         prpr arith false rs
      | (c, 1) :: rs, true ->
         fprintf fmt " + %a" print_const c;
         prpr arith false rs
      | (c, i) :: rs, true ->
         fprintf fmt "%+d * %a" i print_const c;
         prpr arith false rs
      | [], _ -> ()
    in
    prpr arith true ls

  let print_proc fmt s = 
    try Scanf.sscanf (Hstring.view s) "#%d" (fun id -> fprintf fmt "z%d" id)
    with Scanf.Scan_failure _ -> print_name fmt s

  let rec print_args fmt = function
    | [] -> assert false
    | [p] -> print_proc fmt p
    | p :: r -> fprintf fmt "%a %a" print_proc p print_args r

  let rec print_term ~prime fmt = function
    | Term.Const cs -> print_cs fmt cs
    | Term.Elem (s, Var) -> print_proc fmt s
    | Term.Elem (s, Constr) -> fprintf fmt "%a" Hstring.print s
    | Term.Elem (s, Glob) -> fprintf fmt "%a%s" print_name s (spr prime) 
    | Term.Access (a, li) ->
       fprintf fmt "(%a%s %a)" print_name a (spr prime) print_args li
    | Term.Arith (x, cs) -> 
       fprintf fmt "%a%a" (print_term ~prime) x (print_cs ~arith:true) cs

  let rec print_atom ~prime fmt = function
    | Atom.True -> fprintf fmt "true"
    | Atom.False -> fprintf fmt "false"
    | Atom.Comp (x, op, y) -> 
       fprintf fmt "%a %s %a" 
	       (print_term ~prime) x (op_comp op) (print_term ~prime) y
    | Atom.Ite (la, a1, a2) ->
       fprintf fmt "if %a then@ %a@ else@ %a" 
	       (print_atoms ~prime "/\\") (SAtom.elements la) 
	       (print_atom ~prime) a1 (print_atom ~prime) a2

  and print_atoms ~prime sep fmt = function
    | [] -> ()
    | [a] -> print_atom ~prime fmt a
    | a::l -> fprintf fmt "%a %s@ %a" (print_atom ~prime) a sep
		      (print_atoms ~prime sep) l

  let print_satom ~prime fmt sa = 
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

  let print_node ~prime fmt n = 
    begin match Node.variables n with
	  | [] -> () 
	  | args -> fprintf fmt "exists %a:int. %a" 
			  print_args args print_distinct args
    end;
    fprintf fmt "%a" (print_satom ~prime) (Node.litterals n)

  let rec print_invariant ~prime fmt visited = match visited with
    | [] -> assert false
    | [s] -> fprintf fmt "not (%a)" (print_node ~prime) s
    | s ::r -> fprintf fmt "not (%a) /\\@ %a"
		       (print_node ~prime) s (print_invariant ~prime) r


  let rec print_invariant_split ~prime fmt =
    let cpt = ref 1 in
    List.iter (fun s ->
	       fprintf fmt "goal invariant_preserved_%d:\nnot (%a)\n@."
		       !cpt (print_node ~prime) s;
	       incr cpt)

  let rec print_disj ~prime fmt lsa = match lsa with
    | [] -> assert false
    | [sa] -> fprintf fmt "(%a)" (print_satom ~prime) sa
    | sa :: l -> fprintf fmt "(%a) \\/\n%a" (print_satom ~prime) sa
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

  let split_swts_default swts =
    let rec sd acc = function
      | [] -> assert false
      | [d] -> List.rev acc, d
      | s::r -> sd (s::acc) r in
    let swts, (_, default) = sd [] swts in
    swts, default

  let rec print_ite fmt (nt, swts, default) =
    match swts with
    | [] -> 
       fprintf fmt "%a = %a"
               (print_term ~prime:true) nt
	       (print_term ~prime:false) default
    | (cond, t) :: r ->
       fprintf fmt "@[<hov 0>@[<hov 2>if %a then@ %a = %a@]@ \
                    @[<hov 2>else %a@]@]"
	       (print_satom ~prime:false) cond
	       (print_term ~prime:true) nt
	       (print_term ~prime:false) t
	       print_ite (nt, r, default)

  let print_assign fmt (g, gu) =
    match gu with
    | UTerm t -> print_ite fmt (Term.Elem(g, Glob), [], t)
    | UCase swts ->
       let swts, default = split_swts_default swts in
       print_ite fmt (Term.Elem(g, Glob), swts, default)

  let rec add_assign_list globals fmt = function
    | [] -> globals
    | [g,t] -> fprintf fmt "%a" print_assign (g,t);
	       HSet.remove g globals
    | (g,t) :: r ->
       fprintf fmt "%a /\\@ " print_assign (g,t);
       add_assign_list (HSet.remove g globals) fmt r

  let rec print_assigns_unchanged fmt = function
    | [] -> ()
    | [g] -> fprintf fmt "%a' = %a" print_name g print_name g
    | g::r -> fprintf fmt "%a' = %a /\\@ %a" print_name g print_name g
		      print_assigns_unchanged r


  let print_assigns globals fmt ass =
    let globals = List.fold_left (fun acc g -> HSet.add g acc)
				 HSet.empty globals in
    let remaining = add_assign_list globals fmt ass in
    let remaining = HSet.elements remaining in
    if ass <> [] && remaining <> [] then fprintf fmt " /\\@ ";
    print_assigns_unchanged fmt remaining

  let print_update fmt {up_arr=a; up_arg=args; up_swts=swts} =
    let swts, default = split_swts_default swts in
    fprintf fmt "@[<hov 2>forall %a:int.@ " print_args args;
    print_ite fmt (Term.Access (a, args), swts, default);
    fprintf fmt "@]"


  let rec add_updates_list arrays fmt = function
    | [] -> arrays
    | [{up_arr=a} as u] ->
       fprintf fmt "(%a)" print_update u;
       HSet.remove a arrays
    | ({up_arr=a} as u) :: r ->
       fprintf fmt "(%a) /\\@ " print_update u;
       add_updates_list (HSet.remove a arrays) fmt r


  let print_unchanged fmt a =
    let targs, _ = Smt.Symbol.type_of a in
    let args, _ = 
      List.fold_left (fun (acc, n) _ ->
	Hstring.make ("z"^(string_of_int n)) :: acc, n + 1)
	 ([], 1) targs in
    let args = List.rev args in
    fprintf fmt "@[<hov 2>forall %a:int.@ " print_args args;
    fprintf fmt "%a' %a = %a %a"
	    print_name a print_args args 
	    print_name a print_args args;
    fprintf fmt "@]"

  let rec print_all_unchanged fmt = function
    | [] -> ()
    | [a] -> fprintf fmt "(%a) " print_unchanged a
    | a::r -> fprintf fmt "(%a) /\\@ %a"
		      print_unchanged a
		      print_all_unchanged r

  let print_updates arrays fmt upds =
    let arrays = List.fold_left (fun acc a -> Hstring.HSet.add a acc)
				Hstring.HSet.empty arrays in
    let remaining = add_updates_list arrays fmt upds in
    HSet.iter (fprintf fmt "/\\ (%a)@ " print_unchanged) remaining

  let print_updates arrays fmt upds =
    let arrays = List.fold_left (fun acc a -> HSet.add a acc)
				HSet.empty arrays in
    let remaining = add_updates_list arrays fmt upds in
    let remaining = HSet.elements remaining in
    if upds <> [] && remaining <> [] then fprintf fmt " /\\@ ";
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
			 SAtom.subst sigma cond, Term.subst sigma t) swts in
    let swts, default = split_swts_default swts in
    print_ite fmt (Term.Access (a, args), swts, default)

  let rec add_norm_updates vars arrays fmt = function
    | [] -> arrays
    | [{up_arr=a} as u] ->
       fprintf fmt "(%a)" (print_norm_update vars) u;
       HSet.remove a arrays
    | ({up_arr=a} as u) :: r ->
       fprintf fmt "(%a) /\\@ " (print_norm_update vars) u;
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
    | a::r -> fprintf fmt "(%a) /\\@ %a"
		      (print_norm_unchanged vars) a
		      (print_norm_all_unchanged vars) r

  let print_norm_updates arrays fmt upds =
    let vars = max_quant arrays in
    let arrays = List.fold_left (fun acc a -> HSet.add a acc)
				HSet.empty arrays in
    fprintf fmt "forall %a:int.@ " print_args vars;
    let remaining = add_norm_updates vars arrays fmt upds in
    let remaining = HSet.elements remaining in
    if upds <> [] && remaining <> [] then fprintf fmt " /\\@ ";
    print_norm_all_unchanged vars fmt remaining

  let print_transition s fmt {tr_info = t} =
    fprintf fmt "(* transition %a *)@\n" Hstring.print t.tr_name;
    fprintf fmt "(";
    let args =  t.tr_args in
    begin match args with
	  | [] -> fprintf fmt "@,"
	  | _  -> fprintf fmt "exists %a:int. %a@\n" 
			  print_args args print_distinct args
    end;
    fprintf fmt "@[<hov 2>( (* requires *)@\n";
    print_satom ~prime:false fmt t.tr_reqs;
    List.iter (fun (j, disj) ->
      fprintf fmt "\n/\\ (forall %a:int." print_proc j;
      distinct_from_params_imp fmt j args;
      fprintf fmt "\n%a" (print_disj ~prime:false) disj;
      fprintf fmt ")\n";
    ) t.tr_ureq;
    fprintf fmt " )@]";
    if s.t_globals <> [] || s.t_arrays <> [] then
      begin
	fprintf fmt " /\\@ ";
	fprintf fmt "@[<v 2>( (* actions *)@\n";
	print_assigns s.t_globals fmt t.tr_assigns;
	if s.t_globals <> [] && s.t_arrays <> [] then fprintf fmt " /\\@ ";
	(* print_norm_updates s.t_arrays fmt t.tr_upds; *)
	print_updates s.t_arrays fmt t.tr_upds;
	fprintf fmt ")@]";
      end;
    fprintf fmt ")@\n"


  let rec print_transitions_disj s fmt = function
    | [] -> ()
    | [t] -> print_transition s fmt t
    | t :: r -> fprintf fmt "%a\n@.\\/\n\n%a"
			(print_transition s) t 
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

  let print_invnode ~prime fmt s =
    fprintf fmt "not (%a)" (print_node ~prime) s

  let assume_invariant ~prime fmt visited =
    let cpt = ref 0 in
    List.iter (fun s ->
	       incr cpt;
	       fprintf fmt "axiom induction_hypothesis_%d:\n" !cpt;
	       fprintf fmt "    @[%a@]\n@." (print_invnode ~prime) s;
	      ) visited

  let goal_invariant ~prime fmt visited =
    let cpt = ref 0 in
    List.iter (fun s ->
	       incr cpt;
	       fprintf fmt "goal invariant_%d:\n" !cpt;
	       fprintf fmt "    @[%a@]\n@." (print_invnode ~prime) s;
	      ) visited    

  let rec print_str_list_sep sep fmt = function
    | [] -> ()
    | [s] -> fprintf fmt "%s" s
    | s :: r ->
      fprintf fmt "%s" s;
      fprintf fmt sep;
      print_str_list_sep sep fmt r

  let lemma_hint fmt s used inv_names =
    let usedn = List.map (fun n -> fst (NH.find inv_names n)) used in
    let sn' = snd (NH.find inv_names s) in
    fprintf fmt "@[<hov 1>(%a)@]@ /\\@ tau@ ->@ "
      (print_str_list_sep " /\\@ ") usedn;
    fprintf fmt "%s@\n" sn'

  let add_imports fmt s l =
    if need_bool s then fprintf fmt "use import bool.Bool@ ";
    fprintf fmt "use import int.Int@ ";
    if need_real s then fprintf fmt "use import real.Real@ ";
    List.iter (fprintf fmt "use import %s@ ") l;
    fprintf fmt "@\n"

  let add_supplied_invs fmt s =
    let cpt = ref 0 in
    List.iter (fun n ->
        incr cpt;
        fprintf fmt
          "@\n@[<hov 1>axiom user_invariant_%d:@ %a@]@\n"
          !cpt
          (print_invnode ~prime:false) n
      ) s.t_invs


  let capital_base f =
    String.capitalize_ascii
      (sanitize_string_for_why3
         (Filename.chop_extension (Filename.basename f)))

  let theory_decls fmt s =
    let name = (capital_base file)^"_defs" in
    fprintf fmt "@[<v 1>theory %s@\n@\n" name;
    add_imports fmt s [];
    add_type_defs fmt s;
    fprintf fmt "@\n";
    add_decls fmt s;
    add_supplied_invs fmt s;
    fprintf fmt "@\nend@]\n\n@.";
    name

  let theory_invariants_decls fmt s visited imports =
    let hinv_names = NH.create (List.length visited) in
    let name = (capital_base file)^"_invdecls" in
    fprintf fmt "@[<v 1>theory %s@\n@\n" name;
    add_imports fmt s imports;
    List.iter
      (fun n ->
       let invn = "invariant"^(if n.tag < 0 then "X" else "")^
                    (string_of_int (abs n.tag)) in
       let invn' = invn^"'" in
       NH.add hinv_names n (invn, invn');
       fprintf fmt "predicate %s@ " invn;
       fprintf fmt "predicate %s@ " invn'; 
      ) visited;
    fprintf fmt "@]\nend\n\n@.";
    name, hinv_names

  let theory_invariants_defs fmt s hinv_names imports =
    let name = (capital_base file)^"_invdefs" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    NH.iter (fun n (invn, invn') ->
      fprintf fmt "axiom %s_def:\n\
                   %s <-> %a\n@." invn invn (print_invnode ~prime:false) n;
      fprintf fmt "axiom %s_def:\n\
                   %s <-> %a\n@." invn' invn' (print_invnode ~prime:true) n;
    ) hinv_names;
    fprintf fmt "\nend\n\n@.";
    name

  let theory_invariants_preds fmt s visited imports =
    let hinv_names = NH.create (List.length visited) in
    let name = (capital_base file)^"_invpreds" in
    fprintf fmt "@[<v 1>theory %s@ @ " name;
    add_imports fmt s imports;
    List.iter
      (fun n ->
       let invn = "invariant"^(if n.tag < 0 then "X" else "")^
                    (string_of_int (abs n.tag)) in
       let invn' = invn^"'" in
       NH.add hinv_names n (invn, invn');
      ) visited;
    fprintf fmt "(* Inductive invariant *)@\n@\n";
    NH.iter (fun n (invn, invn') ->
      fprintf fmt "@[<hov 1>predicate %s =@\n\
                   %a@]@ @ " invn (print_invnode ~prime:false) n;
    ) hinv_names;
    fprintf fmt "(* Inductive invariant (primed) *)@\n@\n";
    NH.iter (fun n (invn, invn') ->
      fprintf fmt "@[<hov 1>predicate %s =@\n\
                   %a@]@ @ " invn' (print_invnode ~prime:true) n;
    ) hinv_names;
    fprintf fmt "@]\nend\n\n@.";
    name, hinv_names


  let uniq_name n hn =
    let ltr = Hashtbl.fold (fun _ trn acc -> trn :: acc) hn [] in
    let rec uniq_aux n ltr =
      if List.exists ((=) n) ltr then uniq_aux (n^"_") (n::ltr)
      else n
    in
    uniq_aux n ltr


  let theory_transition_decl fmt s imports =
    let tr_names = Hashtbl.create (List.length s.t_trans) in
    let name = (capital_base file)^"_trdecl" in
    fprintf fmt "@[<v 1>theory %s@ @ " name;
    add_imports fmt s imports;
    List.iter (fun tr ->
      let trn = "transition__"^(Hstring.view tr.tr_info.tr_name) in
      let trn = uniq_name trn tr_names in
      Hashtbl.add tr_names tr trn;
      fprintf fmt "predicate %s@ " trn
    ) s.t_trans;
    fprintf fmt "@\npredicate tau@ ";
    fprintf fmt "@]\nend\n\n@.";
    name, tr_names

  let theory_transition_def fmt s tr_names imports =
    let name = (capital_base file)^"_trdefs" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    Hashtbl.iter (fun tr trn ->
      fprintf fmt "axiom %s_def:\n\
                   %s <-> %a\n@." trn trn (print_transition s) tr;
    ) tr_names;
    let ltr = Hashtbl.fold (fun _ trn acc -> trn :: acc) tr_names [] in
    fprintf fmt "axiom tau_def:\n\
                 tau <-> (%a)\n@." (print_str_list_sep " \\/@ ") ltr;
    fprintf fmt "\nend\n\n@.";
    name

  let theory_transition_preds fmt s imports =
    let tr_names = Hashtbl.create (List.length s.t_trans) in
    let name = (capital_base file)^"_trdefs" in
    fprintf fmt "@[<v 1>theory %s@ @ " name;
    add_imports fmt s imports;
    List.iter (fun tr ->
      let trn = "transition__"^(Hstring.view tr.tr_info.tr_name) in
      let trn = uniq_name trn tr_names in
      Hashtbl.add tr_names tr trn;
    ) s.t_trans;
    Hashtbl.iter (fun tr trn ->
      fprintf fmt "@[<hov 1>predicate %s =@\n\
                   %a@]@ @ " trn (print_transition s) tr;
    ) tr_names;
    let ltr = Hashtbl.fold (fun _ trn acc -> trn :: acc) tr_names [] in
    fprintf fmt "@[<hov 1>predicate tau =@\n\
                 %a@]@ @ " (print_str_list_sep " \\/@ ") ltr;
    fprintf fmt "@]\nend\n\n@.";
    name, tr_names

  let theory_init fmt s inv_names imports =
    let name = (capital_base file)^"_initialisation" in
    fprintf fmt "@[<v 1>theory %s@ @ " name;
    add_imports fmt s imports;
    fprintf fmt "@[<hov 1>predicate init =@\n%a@]@ @ " print_init s.t_init;
    let invns = NH.fold (fun _ (invn, _) acc -> invn :: acc) inv_names [] in
    fprintf fmt "@[<hov 1>goal initialisation:@\n\
                 init -> @[<hov 1>(%a)@]@]@ @ "
      (print_str_list_sep " /\\@ ") invns;
    fprintf fmt "@]\nend\n\n@.";
    name


  let remove_definitions fmt inv_names tr_names =
    NH.iter (fun _ (p, p') ->
             fprintf fmt "meta remove_logic predicate %s\n" p;
             fprintf fmt "meta remove_logic predicate %s\n" p';
            ) inv_names;
    Hashtbl.iter (fun _ trn ->
                  fprintf fmt "meta remove_logic predicate %s\n" trn;
                 ) tr_names;
    fprintf fmt "meta remove_logic predicate tau\n@."


  let theory_property fmt s inv_names imports =
    let name = (capital_base file)^"_property" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    let invns = NH.fold (fun _ (invn, _) acc -> invn :: acc) inv_names [] in
    fprintf fmt "@[<hov 1>goal property:@\n\
                 @[<hov 1>(%a)@] ->@ @[<hov 1>(%a)@]@]\n@."
            (print_str_list_sep " /\\@ ") invns
            (print_invariant ~prime:false) s.t_unsafe;
    fprintf fmt "end\n\n@.";
    name

  let theory_preservation fmt s inv_names tr_names imports =
    let name = (capital_base file)^"_preservation" in
    fprintf fmt "@[<v 1>theory %s@ @ " name;
    add_imports fmt s imports;
    (* remove_definitions fmt inv_names tr_names; *)
    let invns, invns' =
      NH.fold (fun _ (invn, invn') (acc, acc') ->
               invn :: acc, invn' :: acc') inv_names ([], []) in
    fprintf fmt "@[<hov 1>goal preservation:@\n\
                 @[<hov 1>(%a)@]@\n/\\@ tau@ ->@ @[<hov 1>(%a)@]@]@ @ "
            (print_str_list_sep " /\\@ ") invns
            (print_str_list_sep " /\\@ ") invns';
    fprintf fmt "@]\nend\n\n@.";
    name


  let remove_unused fmt used s inv_names =
    let usedn = List.map (fun n -> fst (NH.find inv_names n)) used in
    let sn' = snd (NH.find inv_names s) in
    let allu = sn'::usedn in
    NH.iter (fun _ (p, p') ->
             if not (List.mem p allu) then
               fprintf fmt "meta remove_prop prop %s_def\n" p;
             if not (List.mem p' allu) then
               fprintf fmt "meta remove_prop prop %s_def\n" p';
            ) inv_names;
    fprintf fmt "@."
            
      

  let add_lemma_hints fmt clean s hints inv_names imports =
    let cpt = ref 0 in
    NodeMap.fold (fun n used acc ->
        incr cpt;
        let name = (capital_base file)^"_hint_"^(string_of_int !cpt) in
        fprintf fmt "@[<v 1>theory %s@ @ " name;
        add_imports fmt s imports;
        if clean then remove_unused fmt used n inv_names;
        fprintf fmt "@[<hov 1>lemma hint_%d:@\n" !cpt;
        lemma_hint fmt n used inv_names;
        fprintf fmt "@]@]\nend\n\n@.";
        name :: acc
      ) hints []

  exception FoundNode of Node.t
  let find_by_tag id visited =
    try
      List.iter (fun n ->
                       (* eprintf "%d@." n.tag; *)
                 if n.tag = id then raise (FoundNode n)) visited;
      (* eprintf "Not found %d@." id; *)
      raise Not_found
    with FoundNode n -> n

  let add_si = List.fold_left (fun acc i -> SI.add i acc)

  let extract_hints s visited =
    if not quiet then printf "Computing hints for certificate ... @?";
    if not quiet && verbose >= 1 then printf "@.";
    let hints = List.fold_left
      (fun hints phi ->
       let ls, post = Pre.pre_image s.t_trans phi in
       let used =
         List.fold_left
           (fun used p ->
            (* match Fixpoint.pure_smt_check p visited with *)
            match Fixpoint.check p visited with
            | None ->
               eprintf
                 "Was not able to reverify partial inductiveness of:\n%a@."
                 Node.print p;
               assert false
            | Some db -> 
               let db = List.filter (fun id -> not (id = p.tag)) db in
               add_si used db
           ) SI.empty (ls@post)
       in
       if not quiet && verbose >= 1 then begin
         printf "Node : %d\t======> " phi.tag ;
         printf " [[ %d used ]] " (SI.cardinal used);
         SI.iter (fun i -> printf ", %d" i) used;
         printf "@.";
       end;
       (* printf "\n      %a@." SAtom.print_inline (Node.litterals phi); *)
       let used_nodes = List.map (fun id -> find_by_tag id visited)
                                 (SI.elements used) in
       NodeMap.add phi used_nodes hints
      ) NodeMap.empty visited
    in
    if not quiet then printf "done.@.";
    hints


  let theories_hints fmt ?(clean=false) s visited inv_names imports =
    (* fprintf fmt "\naxiom transition_relation:@."; *)
    (* fprintf fmt "%a\n@." transition_relation s; *)
    let hints = extract_hints s visited in
    add_lemma_hints fmt clean s hints inv_names imports


  let certificate_w_axioms s visited =
    let why_certif = cert_file_name () in
    let cout = open_out why_certif in
    let fmt = formatter_of_out_channel cout in
    let decls = theory_decls fmt s in
    let thinv, inv_names = theory_invariants_decls fmt s visited [decls] in
    let thinv_def = theory_invariants_defs fmt s inv_names [decls; thinv] in
    let thtau, tr_names = theory_transition_decl fmt s [decls] in
    let thtau_def = theory_transition_def fmt s tr_names [decls; thtau] in
    ignore(theory_init fmt s inv_names [decls; thinv; thinv_def]);
    ignore(theory_property fmt s inv_names [decls; thinv; thinv_def]);
    let thhints = theories_hints fmt ~clean:true s visited inv_names
                  [decls; thinv; thinv_def; thtau; thtau_def] in
    ignore (theory_preservation fmt s inv_names tr_names ([decls; thinv; thtau] @ thhints));
    flush cout; close_out cout;
    printf "Why3 certificate created in %s@." why_certif


  let certificate_w_predicates s visited =
    let why_certif = cert_file_name () in
    let cout = open_out why_certif in
    let fmt = formatter_of_out_channel cout in
    let decls = theory_decls fmt s in
    let thinv, inv_names = theory_invariants_preds fmt s visited [decls] in
    let thtau, tr_names = theory_transition_preds fmt s [decls] in
    ignore(theory_init fmt s inv_names [decls; thinv]);
    ignore(theory_property fmt s inv_names [decls; thinv]);
    let thhints = theories_hints fmt s visited inv_names
                  [decls; thinv; thtau] in
    ignore (theory_preservation fmt s inv_names tr_names ([decls; thinv; thtau] @ thhints));
    flush cout; close_out cout;
    printf "Why3 certificate created in %s@." why_certif

  let certificate = certificate_w_predicates

end





(*************************** EXPERIMENTAL STUFF *****************************)

module Why3_INST = struct
    

  module CompInt = struct type t = int let compare = Pervasives.compare end

  module NodeH = struct
    type t = Node.t
    let compare n1 n2 = Pervasives.compare n1.tag n2.tag
    let equal n1 n2 = n1.tag == n2.tag
    let hash n = n.tag
  end

  module SPinst = Set.Make (struct
    type t = Node.t * Variable.subst
    let compare (n1, s1) (n2, s2) = 
      let c = Pervasives.compare n1.tag n2.tag in
      if c = 0 then Pervasives.compare s1 s2 else c
  end)

  module SI = Set.Make(CompInt)
  module MI = Map.Make(CompInt)
  module NodeMap = Map.Make(NodeH)
  module NH = Hashtbl.Make(NodeH)
  module FixpointC = Fixpoint.FixpointCertif


  let print_name fmt s =
    fprintf fmt "%s" (String.uncapitalize_ascii (Hstring.view s))

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

  let print_decl ?(prime=false) ?(const=false) fmt s =
    let t_args, t_ret = Smt.Symbol.type_of s in
    fprintf fmt "%s %a%s "
      (if const then "constant" else "function")
      print_name s (spr prime);
    List.iter (fprintf fmt "%a " print_type) t_args;
    fprintf fmt ": %a" print_type t_ret

  let add_decls fmt s =
    let d = List.iter
        (fprintf fmt "%a@." (print_decl ~prime:false ~const:false)) in
    let c = List.iter
        (fprintf fmt "%a@." (print_decl ~prime:false ~const:true)) in
    let d_prime = List.iter
        (fprintf fmt "%a@." (print_decl ~prime:true ~const:false)) in
    d s.t_globals; d_prime s.t_globals;
    d s.t_arrays; d_prime s.t_arrays;
    c s.t_consts

  
  let op_comp = function Eq -> "=" | Lt -> "<" | Le -> "<=" | Neq -> "<>"

  let print_const fmt = function
    | ConstInt n -> fprintf fmt "%s" (Num.string_of_num n)
    | ConstReal n -> fprintf fmt "%F" (Num.float_of_num n)
    | ConstName n -> fprintf fmt "%a" print_name n

  let print_cs fmt cs =
    MConst.iter 
      (fun c i ->
       fprintf fmt " %s %a" 
	       (if i = 1 then "+" else if i = -1 then "-" 
	        else if i < 0 then "- "^(string_of_int (abs i)) 
	        else "+ "^(string_of_int (abs i)))
	       print_const c) cs

  let print_proc fmt s = 
    try Scanf.sscanf (Hstring.view s) "#%d" (fun id -> fprintf fmt "z%d" id)
    with Scanf.Scan_failure _ -> print_name fmt s

  let rec print_args fmt = function
    | [] -> assert false
    | [p] -> print_proc fmt p
    | p :: r -> fprintf fmt "%a %a" print_proc p print_args r

  let rec print_term ~prime fmt = function
    | Term.Const cs -> print_cs fmt cs
    | Term.Elem (s, Var) -> print_proc fmt s
    | Term.Elem (s, Constr) -> fprintf fmt "%a" Hstring.print s
    | Term.Elem (s, Glob) -> fprintf fmt "%a%s" print_name s (spr prime) 
    | Term.Access (a, li) ->
       fprintf fmt "(%a%s %a)" print_name a (spr prime) print_args li
    | Term.Arith (x, cs) -> 
       fprintf fmt "@[(%a%a)@]" (print_term ~prime) x print_cs cs

  let rec print_atom ~prime fmt = function
    | Atom.True -> fprintf fmt "true"
    | Atom.False -> fprintf fmt "false"
    | Atom.Comp (x, op, y) -> 
       fprintf fmt "%a %s %a" 
	       (print_term ~prime) x (op_comp op) (print_term ~prime) y
    | Atom.Ite (la, a1, a2) ->
       fprintf fmt "@[(if %a then@ %a@ else@ %a)@]" 
	       (print_atoms ~prime "/\\") (SAtom.elements la) 
	       (print_atom ~prime) a1 (print_atom ~prime) a2

  and print_atoms ~prime sep fmt = function
    | [] -> ()
    | [a] -> print_atom ~prime fmt a
    | a::l -> fprintf fmt "%a %s@\n%a" (print_atom ~prime) a sep
		      (print_atoms ~prime sep) l

  let print_satom ~prime fmt sa = 
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

  let print_exists_disj fmt args =
    match args with
    | [] -> () 
    | args -> fprintf fmt "exists %a:int. %a" 
		      print_args args print_distinct args

  let print_cubef ~prime fmt n =
    fprintf fmt "%a" (print_satom ~prime) (Node.litterals n)

  let print_node ~prime fmt n =
    print_exists_disj fmt (Node.variables n);
    print_cubef ~prime fmt n

  let rec print_invariant ~prime fmt visited = match visited with
    | [] -> assert false
    | [s] -> fprintf fmt "not (%a)" (print_node ~prime) s
    | s ::r -> fprintf fmt "not (%a) /\\\n%a"
		       (print_node ~prime) s (print_invariant ~prime) r


  let rec print_invariant_split ~prime fmt =
    let cpt = ref 1 in
    List.iter (fun s ->
	       fprintf fmt "goal invariant_preserved_%d:\nnot (%a)\n@."
		       !cpt (print_node ~prime) s;
	       incr cpt)

  let rec print_disj ~prime fmt lsa = match lsa with
    | [] -> assert false
    | [sa] -> fprintf fmt "(%a)" (print_satom ~prime) sa
    | sa :: l -> fprintf fmt "(%a) \\/\n%a" (print_satom ~prime) sa
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

  let split_swts_default swts =
    let rec sd acc = function
      | [] -> assert false
      | [d] -> List.rev acc, d
      | s::r -> sd (s::acc) r in
    let swts, (_, default) = sd [] swts in
    swts, default

  let rec print_ite fmt (nt, swts, default) =
    match swts with
    | [] -> 
       fprintf fmt "%a = %a"
               (print_term ~prime:true) nt
	       (print_term ~prime:false) default
    | (cond, t) :: r ->
       fprintf fmt "(if %a then\n %a = %a\nelse@? %a)"
	       (print_satom ~prime:false) cond
	       (print_term ~prime:true) nt
	       (print_term ~prime:false) t
	       print_ite (nt, r, default)

  let print_assign fmt (g, gu) =
    match gu with
    | UTerm t -> print_ite fmt (Term.Elem(g, Glob), [], t)
    | UCase swts ->
       let swts, default = split_swts_default swts in
       print_ite fmt (Term.Elem(g, Glob), swts, default)

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

  let print_update fmt {up_arr=a; up_arg=args; up_swts=swts} =
    let swts, default = split_swts_default swts in
    fprintf fmt "forall %a:int.\n" print_args args;
    print_ite fmt (Term.Access (a, args), swts, default)


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
			 SAtom.subst sigma cond, Term.subst sigma t) swts in
    let swts, default = split_swts_default swts in
    print_ite fmt (Term.Access (a, args), swts, default)

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

  let print_transition s fmt {tr_info = t} =
    fprintf fmt "(* transition %a *)\n" Hstring.print t.tr_name;
    fprintf fmt "(";
    let args =  t.tr_args in
    begin match args with
	  | [] -> ()
	  | _  -> fprintf fmt "exists %a:int. %a\n" 
			  print_args args print_distinct args
    end;
    fprintf fmt "( (* requires *)\n";
    print_satom ~prime:false fmt t.tr_reqs;
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
    | [t] -> print_transition s fmt t
    | t :: r -> fprintf fmt "%a\n@.\\/\n\n%a"
			(print_transition s) t 
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

  let print_invnode ~prime fmt s =
    fprintf fmt "not (%a)" (print_node ~prime) s

  let print_invexi ~prime name fmt s =
    fprintf fmt "not (%a (%s_cube %a))"
    print_exists_disj (Node.variables s)
    (name^(if prime then "'" else ""))
    print_args (Node.variables s)


  let assume_invariant ~prime fmt visited =
    let cpt = ref 0 in
    List.iter (fun s ->
	       incr cpt;
	       fprintf fmt "axiom induction_hypothesis_%d:\n" !cpt;
	       fprintf fmt "    @[%a@]\n@." (print_invnode ~prime) s;
	      ) visited

  let goal_invariant ~prime fmt visited =
    let cpt = ref 0 in
    List.iter (fun s ->
	       incr cpt;
	       fprintf fmt "goal invariant_%d:\n" !cpt;
	       fprintf fmt "    @[%a@]\n@." (print_invnode ~prime) s;
	      ) visited    

  let rec print_str_list_sep sep fmt = function
    | [] -> ()
    | [s] -> fprintf fmt "%s" s
    | s :: r -> fprintf fmt "%s%s%a" s sep (print_str_list_sep sep) r

  let rec print_fct_list_sep sep fmt = function
    | [] -> ()
    | [s, args] -> fprintf fmt "(%s %a)" s print_args args
    | (s, args) :: r -> fprintf fmt "(%s %a)%s%a" s  print_args args sep
                        (print_fct_list_sep sep) r

  let lemma_hint fmt s used inv_names =
    let usedn =
      List.map (fun (n, sigma) ->
        (* eprintf "fc : (%d) %a@." n.tag Node.print n;  *)
        let name = fst (NH.find inv_names n) in
        let args = List.map snd sigma in
        name^"_cube", args
      ) used in
    let sn' = (snd (NH.find inv_names s))^"_cube" in
    fprintf fmt "    @[(%a /\\ tau)@]\n" (print_fct_list_sep " /\\ ") usedn;
    fprintf fmt "    -> (%s %a)\n@." sn' print_args (Node.variables s)

  let add_imports fmt s l =
    if need_bool s then fprintf fmt "use import bool.Bool@ ";
    fprintf fmt "use import int.Int@ ";
    if need_real s then fprintf fmt "use import real.Real@ ";
    List.iter (fprintf fmt "use import %s@ ") l;
    fprintf fmt "@\n"

  
  let add_supplied_invs fmt s =
    let cpt = ref 0 in
    List.iter (fun n ->
        incr cpt;
        fprintf fmt
          "@\n@[<hov 1>axiom user_invariant_%d:@ %a@]@\n"
          !cpt
          (print_invnode ~prime:false) n
      ) s.t_invs

  
  let capital_base f =
    String.capitalize_ascii (Filename.chop_extension (Filename.basename f))

  let theory_decls fmt s =
    let name = (capital_base file)^"_defs" in
    fprintf fmt "@[<v 1>theory %s@\n@\n" name;
    add_imports fmt s [];
    add_type_defs fmt s;
    fprintf fmt "@\n";
    add_decls fmt s;
    add_supplied_invs fmt s;
    fprintf fmt "@\nend@]\n\n@.";
    name

  let theory_invariants_decls fmt s visited imports =
    let hinv_names = NH.create (List.length visited) in
    let name = (capital_base file)^"_invdecls" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    List.iter
      (fun n ->
       let invn = "invariant"^(if n.tag < 0 then "X" else "")^
                    (string_of_int (abs n.tag)) in
       let invn' = invn^"'" in
       NH.add hinv_names n (invn, invn');
       fprintf fmt "predicate %s_cube\n" invn;
       fprintf fmt "predicate %s_cube\n" invn';
       fprintf fmt "predicate %s\n" invn;
       fprintf fmt "predicate %s\n" invn';
      ) visited;
    fprintf fmt "\nend\n\n@.";
    name, hinv_names

  let theory_invariants_defs fmt s hinv_names imports =
    let name = (capital_base file)^"_invdefs" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    NH.iter (fun n (invn, invn') ->
      fprintf fmt "axiom %s_cube_def:\n\
                   %s_cube <-> %a\n@." invn invn (print_cubef ~prime:false) n;
      fprintf fmt "axiom %s_cube_def:\n\
                   %s_cube <-> %a\n@." invn' invn' (print_cubef ~prime:true) n;
      fprintf fmt "axiom %s_def:\n\
                   %s <-> %a\n@." invn invn (print_invexi ~prime:false invn) n;
      fprintf fmt "axiom %s_def:\n\
                   %s <-> %a\n@." invn' invn' (print_invexi ~prime:true invn) n;
    ) hinv_names;
    fprintf fmt "\nend\n\n@.";
    name

  let print_pred_args_proc fmt = function
    | [] -> ()
    | args ->
       fprintf fmt "(%a:int)" print_args args

  let theory_invariants_preds fmt s visited imports =
    let hinv_names = NH.create (List.length visited) in
    let name = (capital_base file)^"_invpreds" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    List.iter
      (fun n ->
       let invn = "invariant"^(if n.tag < 0 then "X" else "")^
                    (string_of_int (abs n.tag)) in
       let invn' = invn^"'" in
       NH.add hinv_names n (invn, invn');
      ) visited;
    NH.iter (fun n (invn, invn') ->
      fprintf fmt "predicate %s_cube %a=\n\
                   %a\n@." invn print_pred_args_proc (Node.variables n)
              (print_cubef ~prime:false) n;
      fprintf fmt "predicate %s_cube %a=\n\
                   %a\n@." invn' print_pred_args_proc (Node.variables n)
              (print_cubef ~prime:true) n;
      fprintf fmt "predicate %s =\n\
                   %a\n@." invn (print_invexi ~prime:false invn) n;
      fprintf fmt "predicate %s =\n\
                   %a\n@." invn' (print_invexi ~prime:true invn) n;
    ) hinv_names;
    fprintf fmt "\nend\n\n@.";
    name, hinv_names


  let uniq_name n hn =
    let ltr = Hashtbl.fold (fun _ trn acc -> trn :: acc) hn [] in
    let rec uniq_aux n ltr =
      if List.exists ((=) n) ltr then uniq_aux (n^"_") (n::ltr)
      else n
    in
    uniq_aux n ltr


  let theory_transition_decl fmt s imports =
    let tr_names = Hashtbl.create (List.length s.t_trans) in
    let name = (capital_base file)^"_trdecl" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    List.iter (fun tr ->
      let trn = "transition__"^(Hstring.view tr.tr_info.tr_name) in
      let trn = uniq_name trn tr_names in
      Hashtbl.add tr_names tr trn;
      fprintf fmt "predicate %s\n" trn
    ) s.t_trans;
    fprintf fmt "\npredicate tau\n";
    fprintf fmt "\nend\n\n@.";
    name, tr_names

  let theory_transition_def fmt s tr_names imports =
    let name = (capital_base file)^"_trdefs" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    Hashtbl.iter (fun tr trn ->
      fprintf fmt "axiom %s_def:\n\
                   %s <-> %a\n@." trn trn (print_transition s) tr;
    ) tr_names;
    let ltr = Hashtbl.fold (fun _ trn acc -> trn :: acc) tr_names [] in
    fprintf fmt "axiom tau_def:\n\
                 tau <-> (%a)\n@." (print_str_list_sep " \\/ ") ltr;
    fprintf fmt "\nend\n\n@.";
    name

  let theory_transition_preds fmt s imports =
    let tr_names = Hashtbl.create (List.length s.t_trans) in
    let name = (capital_base file)^"_trdefs" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    List.iter (fun tr ->
      let trn = "transition__"^(Hstring.view tr.tr_info.tr_name) in
      let trn = uniq_name trn tr_names in
      Hashtbl.add tr_names tr trn;
    ) s.t_trans;
    Hashtbl.iter (fun tr trn ->
      fprintf fmt "predicate %s =\n\
                   %a\n@." trn (print_transition s) tr;
    ) tr_names;
    let ltr = Hashtbl.fold (fun _ trn acc -> trn :: acc) tr_names [] in
    fprintf fmt "predicate tau =\n\
                 (%a)\n@." (print_str_list_sep " \\/ ") ltr;
    fprintf fmt "\nend\n\n@.";
    name, tr_names

  let theory_init fmt s inv_names imports =
    let name = (capital_base file)^"_initialisation" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    fprintf fmt "predicate init =\n    %a\n@." print_init s.t_init;
    let invns = NH.fold (fun _ (invn, _) acc -> invn :: acc) inv_names [] in
    fprintf fmt "goal initialisation:\n    \
                 init -> (%a)\n@." (print_str_list_sep " /\\ ") invns;
    fprintf fmt "\nend\n\n@.";
    name


  let remove_definitions fmt inv_names tr_names =
    NH.iter (fun _ (p, p') ->
             fprintf fmt "meta remove_logic predicate %s\n" p;
             fprintf fmt "meta remove_logic predicate %s\n" p';
            ) inv_names;
    Hashtbl.iter (fun _ trn ->
                  fprintf fmt "meta remove_logic predicate %s\n" trn;
                 ) tr_names;
    fprintf fmt "meta remove_logic predicate tau\n@."


  let theory_property fmt s inv_names imports =
    let name = (capital_base file)^"_property" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    let invns = NH.fold (fun _ (invn, _) acc -> invn :: acc) inv_names [] in
    fprintf fmt "goal property:\n    \
                 (%a) -> (%a)\n@."
            (print_str_list_sep " /\\ ") invns
            (print_invariant ~prime:false) s.t_unsafe;
    fprintf fmt "\nend\n\n@.";
    name

  let theory_preservation fmt s inv_names tr_names imports =
    let name = (capital_base file)^"_preservation" in
    fprintf fmt "theory %s\n@." name;
    add_imports fmt s imports;
    (* remove_definitions fmt inv_names tr_names; *)
    let invns, invns' =
      NH.fold (fun _ (invn, invn') (acc, acc') ->
               invn :: acc, invn' :: acc') inv_names ([], []) in
    fprintf fmt "goal preservation:\n    \
                 (%a /\\ tau)\n    ->\n    (%a)\n@."
            (print_str_list_sep " /\\ ") invns
            (print_str_list_sep " /\\ ") invns';
    fprintf fmt "\nend\n\n@.";
    name


  let remove_unused fmt used s inv_names =
    let usedn = List.map (fun n -> fst (NH.find inv_names n)) used in
    let sn' = snd (NH.find inv_names s) in
    let allu = sn'::usedn in
    NH.iter (fun _ (p, p') ->
             if not (List.mem p allu) then
               fprintf fmt "meta remove_prop prop %s_def\n" p;
             if not (List.mem p' allu) then
               fprintf fmt "meta remove_prop prop %s_def\n" p';
            ) inv_names;
    fprintf fmt "@."
            
      
  let print_proc_constants fmt s =
    List.iter (fprintf fmt "constant %a : int\n" print_proc) (Node.variables s)

  let add_lemma_hints fmt clean s hints inv_names imports =
    let cpt = ref 0 in
    NodeMap.fold (fun n used acc ->
                  incr cpt;
                  let name = (capital_base file)^"_hint_"^(string_of_int !cpt) in
                  fprintf fmt "theory %s\n@." name;
                  add_imports fmt s imports;
                  (* if clean then remove_unused fmt used n inv_names; *)
                  print_proc_constants fmt n;
                  fprintf fmt "lemma hint_%d:\n" !cpt;
                  lemma_hint fmt n used inv_names;
                  fprintf fmt "@.";
                  fprintf fmt "\nend\n\n@.";
                  name :: acc
                 ) hints []

  exception FoundNode of Node.t
  let find_by_tag id visited =
    try
      List.iter (fun n ->
                       (* eprintf "%d@." n.tag; *)
                 if n.tag = id then raise (FoundNode n)) visited;
      (* eprintf "Not found %d@." id; *)
      raise Not_found
    with FoundNode n -> n

  let add_si = List.fold_left (fun acc i -> SI.add i acc)

  let add_pinst = List.fold_left (fun acc i -> SPinst.add i acc)

  let extract_hints s visited =
    if not quiet then printf "Computing hints for certificate ... @?";
    if not quiet && verbose >= 1 then printf "@.";
    let hints = List.fold_left
      (fun hints phi ->
       let ls, post = Pre.pre_image s.t_trans phi in
       let used =
         List.fold_left
           (fun used p ->
            (* match Fixpoint.pure_smt_check p visited with *)
            add_pinst used (FixpointC.useful_instances p visited)
           ) SPinst.empty (ls@post)
       in
       if not quiet && verbose >= 1 then begin
         printf "Node : %d\t======> " phi.tag ;
         printf " [[ %d used ]] " (SPinst.cardinal used);
         (* SPinst.iter (fun i -> printf ", %d" i) used; *)
         printf "@.";
       end;
       NodeMap.add phi (SPinst.elements used) hints
      ) NodeMap.empty visited
    in
    if not quiet then printf "done.@.";
    hints


  let theories_hints fmt ?(clean=false) s visited inv_names imports =
    (* fprintf fmt "\naxiom transition_relation:@."; *)
    (* fprintf fmt "%a\n@." transition_relation s; *)
    let hints = extract_hints s visited in
    add_lemma_hints fmt clean s hints inv_names imports


  let certificate_w_axioms s visited =
    let why_certif = cert_file_name () in
    let cout = open_out why_certif in
    let fmt = formatter_of_out_channel cout in
    let decls = theory_decls fmt s in
    let thinv, inv_names = theory_invariants_decls fmt s visited [decls] in
    let thinv_def = theory_invariants_defs fmt s inv_names [decls; thinv] in
    let thtau, tr_names = theory_transition_decl fmt s [decls] in
    let thtau_def = theory_transition_def fmt s tr_names [decls; thtau] in
    ignore(theory_init fmt s inv_names [decls; thinv; thinv_def]);
    ignore(theory_property fmt s inv_names [decls; thinv; thinv_def]);
    let thhints = theories_hints fmt ~clean:true s visited inv_names
                  [decls; thinv; thinv_def; thtau; thtau_def] in
    ignore (theory_preservation fmt s inv_names tr_names ([decls; thinv; thtau] @ thhints));
    flush cout; close_out cout;
    printf "Why3 certificate created in %s@." why_certif


  let certificate_w_predicates s visited =
    let why_certif = cert_file_name () in
    let cout = open_out why_certif in
    let fmt = formatter_of_out_channel cout in
    let decls = theory_decls fmt s in
    let thinv, inv_names = theory_invariants_preds fmt s visited [decls] in
    let thtau, tr_names = theory_transition_preds fmt s [decls] in
    ignore(theory_init fmt s inv_names [decls; thinv]);
    ignore(theory_property fmt s inv_names [decls; thinv]);
    let thhints = theories_hints fmt s visited inv_names
                  [decls; thinv; thtau] in
    ignore (theory_preservation fmt s inv_names tr_names ([decls; thinv; thtau] @ thhints));
    flush cout; close_out cout;
    printf "Why3 certificate created in %s@." why_certif

  let certificate = certificate_w_predicates

end


(************************* END EXPERIMENTAL STUFF ***************************)




module Empty : S = struct

  let certificate _ _ = ()

end


let select_format =
  match Options.trace with
  | AltErgoTr -> (module AltErgo : S)
  | WhyTr -> (module Why3 : S)
  | WhyInst -> (module Why3_INST : S)
  | NoTrace -> (module Empty)

module Selected : S = struct 
  include (val select_format)

  (* Sort nodes first *)
  let certificate s visited =
    if Options.trace <> NoTrace then begin
        Util.TimeCertificate.start ();
        let visited = List.fast_sort Node.compare_by_breadth visited in
        certificate s visited;
        Util.TimeCertificate.pause ();
        let f = cert_file_name () in
        Stats.print_stats_certificate visited f
      end

end
