open Ast
open Types
open Interpret_errors
open Interpret_types
open OcamlCanvas.V1



let interpret_bool = ref true

  
let eval_arith ta env ty =
  let term, im =
    match ta with
      | Arith(t, im) -> t, im
      | _ -> assert false
  in
  let c = int_of_consts im in
  match term with
    | Elem(_, SystemProcs) ->
      let vv = !sys_procs + c in 
      if is_semaphore ty then VSemaphore vv
      else if is_int ty then VInt vv
      else if is_real ty then VReal (float_of_int vv)
      else assert false
    | _ -> begin
      let v = Env.find term env in  
      match v.value with
	| VInt i -> VInt (c+i)
	| VReal i -> assert false
	| VSemaphore i -> VSemaphore (c+i)
	| _ ->assert false
    end


let semaphore_init s =
  match s with
    | Const i -> let x = int_of_consts i in VSemaphore x
    | Elem(_, SystemProcs) -> VSemaphore !sys_procs
    | Arith _ -> VArith s
    | _ -> assert false
					 					 

let throwaway = Elem(Hstring.make "UNDEF", Glob)

let get_proc p =
  let proc = Hstring.view p in
  let c = int_of_string(String.sub proc 1 1) in
  let c = c mod ((Options.get_interpret_procs ()) -1) in
  Elem(Hstring.make ("#"^(string_of_int c)), Var)
  

let terms_of_procs l = List.map (fun x -> Elem (x, Var)) l

let all_constr_terms () =
  List.rev_map (fun x -> Elem (x, Constr)) (Smt.Type.all_constructors ())

let check_undef v = Term.compare v throwaway = 0 

let rec all_arrange n l =
  if n <= 0 then []
  else (
  match n with
    | 1 -> List.map (fun x -> [x]) l
    | _ -> 
        List.fold_left (fun acc l' ->
          List.fold_left (fun acc x -> 
	    if List.exists (fun el -> el = x) l' then acc else 
	    (x :: l') :: acc) acc l
        ) [] (all_arrange (n - 1) l))
  

let gen_array name procs = 
  List.fold_left (fun acc a ->
    let indexes = Variable.all_arrangements_arity a procs in
    List.fold_left (fun acc lp ->
      Access (a, lp):: acc)
      acc indexes)
    [] [name]

let gen_array_eq_proc name procs = 
  List.fold_left (fun acc a ->
    let indexes = Variable.all_arrangements_arity a procs in
    List.fold_left (fun acc lp ->
      (Access (a, lp),lp):: acc)
      acc indexes)
    [] [name]

let gen_array_combs name procs = 
  List.fold_left (fun acc a ->
    let indexes = Variable.all_arrangements_arity a procs in
    List.fold_left (fun acc lp ->
      lp:: acc)
      acc indexes)
    [] [name]
    
let fresh = 
  let cpt = ref 0 in
  fun () -> incr cpt; !cpt

      
let init_vals env init =
  if Options.debug_interpreter then Format.eprintf "Init_vals:@.";
  let procs = Variable.give_procs (Options.get_interpret_procs ()) in
  let _, dnf = init in
  List.fold_left (fun acc el ->
    SAtom.fold (fun atom sacc -> 
      match atom with	  	  
	| Comp (t1, Eq, t2) ->
	  if Options.debug_interpreter then
	    Format.eprintf "Treating %a = %a @." Term.print t1 Term.print t2;
	  begin
	    match t1, t2 with 
	      | Elem (_, Glob), Elem (_, Glob) ->		
		let temp = Env.add t2 t1 sacc in
		  Env.add t1 t2 temp 

	      | Elem(_, Glob), Elem(_, (Var|Constr)) -> Env.add t1 t2 sacc
	      | Elem(_, (Var|Constr)), Elem(_, Glob) -> Env.add t2 t1 sacc
		
	      | Elem(_, Glob), Const cs -> Env.add t1 t2 sacc 

	      | Access(n, _), Elem(_,Var) -> 
		let arr = gen_array_eq_proc n procs in
		List.fold_left(fun acc3 (x,v) ->
		  match v with
		    | [el] -> Env.add x (Elem (el,Var)) acc3
		    | _ -> assert false
		   ) sacc arr		
	      | Access(n, _), _ -> 
		let arr = gen_array n procs in
		List.fold_left(fun acc3 x ->		  
		  Env.add x t2 acc3 ) sacc arr
	      | _ , Access(n,_) ->		
		let arr = gen_array n procs in
		List.fold_left(fun acc3 x ->
		  Env.add x t1 acc3 ) sacc arr
	      | Elem(_, Glob) , Elem(_, SystemProcs) -> Env.add t1 t2 sacc
	      | Elem(_, Glob), Arith(tt, im) ->
		Env.add t1 t2 sacc
		
		
	      | _ -> assert false
		  	     		    
	  end 	    	   	  
	| Comp (t1, Neq, t2) -> assert false
	| Comp (t1, Lt, t2) -> assert false
	| Comp (t1, Le, t2) -> assert false
	| True -> assert false
	| False -> assert false
	| Ite _ -> assert false
	  
    ) el acc
  ) env dnf
      

let check_unsafe (env,_,_,_) unsafe =
  (*unsafe = (loc * variable * satom) list *)
  let procs = Variable.give_procs (Options.get_interpret_procs ()) in 
  let v = Env.fold (fun key {value = el} acc ->
    match el with
      | VGlob el -> SAtom.add (Comp(key, Eq, Elem(el, Glob))) acc 
      | VProc el -> SAtom.add (Comp(key, Eq, Elem(el, Var))) acc
      | VConstr el -> SAtom.add (Comp(key, Eq, Elem(el, Constr))) acc
      | VAccess(el,vl) -> SAtom.add (Comp(key, Eq, Access(el, vl))) acc
      | _-> acc   
  ) env SAtom.empty
  in
  List.iter (fun (_,vs, satom) ->
    let all_procs = Variable.all_permutations vs procs in
    List.iter (fun pl ->
      try
	let sa = SAtom.subst pl satom in
	Prover.reached vs v sa; raise (TopError Reached)
      with
	| Smt.Unsat  _ -> ()
	| TopError Reached -> raise (TopError Unsafe)
    ) all_procs      
  ) unsafe


let add_sub_manip manip sigma =
  match manip with 
    | ProcManip([t], PlusOne) ->
      let t = Term.subst sigma t in 
      begin
	match t with
	  | Elem(n, Var) -> let ni = Variable.number n in
			    let ni = ni + 1 in
			    let ns = string_of_int ni in
			    let h = Hstring.make ("#"^ns) in
			    {value = VProc h; typ = Smt.Type.type_proc }
	  | _ -> assert false
      end
    | ProcManip([t], MinusOne) ->
      begin
	match t with
	  | Elem(n, Var) -> let ni = Variable.number n in
			    let ni = ni - 1 in
			    let ns = string_of_int ni in
			    let h = Hstring.make ("#"^ns) in
			    { value = VProc h; typ = Smt.Type.type_proc}
	  | _ -> assert false
      end
    | _ -> assert false

  
let check_comp t1 t2 env sigma op =
  match t1, t2 with      
    | Elem(_, Glob), Elem(_, Glob) ->
      let ev1 = Env.find t1 env in
      let ev2 = Env.find t2 env in
      interpret_comp (compare_interp_val ev1 ev2) op
	
    | Elem(_, Glob), Elem(_, (Constr|Var)) ->
      let ev1 = Env.find t1 env in
      let t2 = Term.subst sigma t2 in 
      interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op
	  
    | Elem (_, (Constr|Var)), Elem(_, Glob) ->
      let ev1 = Env.find t2 env in
      let t1 = Term.subst sigma t1 in 
      interpret_comp (compare_interp_val (to_interpret t1 ) ev1) op
	
    | Elem(_, Glob), Access _ ->
      let t = Term.subst sigma t2 in
      let ev1 = Env.find t1 env in
      let ev2 = Env.find t env in
      interpret_comp (compare_interp_val ev1 ev2) op
	
    | Access _, Elem(_, Glob) ->
      let t = Term.subst sigma t1 in
      let ev1 = Env.find t env in
      let ev2 = Env.find t2 env in
      interpret_comp (compare_interp_val ev1 ev2) op
	
    | Elem (_, (Constr|Var)), Access _ ->
	
      let t = Term.subst sigma t2 in
      let ev1 = Env.find t env in
      let t1 = Term.subst sigma t1 in 
      interpret_comp (compare_interp_val (to_interpret t1 ) ev1) op	
	
    | Access _, Elem (_, (Constr|Var))->
      let t = Term.subst sigma t1 in
      let ev1 = Env.find t env in
      let t2 = Term.subst sigma t2 in 
      interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op
	
    | Elem(n1,Constr), Elem(n2,Constr) -> interpret_comp (Hstring.compare n1 n2) op

    | Access _, Const msc->
      let t = Term.subst sigma t1 in
      let ev1 = Env.find t env in
      let t2 = Term.subst sigma t2 in 
      interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op
	  
    | Elem(n1, Glob), Const msc ->
      let t1 = Term.subst sigma t1 in
      let ev1 = Env.find t1 env in
      interpret_comp (compare_interp_val ev1 (to_interpret t2)) op

    | Const msc , Elem(n1,Glob)->
      let t2 = Term.subst sigma t2 in
      let ev1 = Env.find t2 env in
      interpret_comp (compare_interp_val (to_interpret t1) ev1) op
	
	
    | Elem(n1, Glob), Arith(aterm, msc) ->
      let t1 = Term.subst sigma t1 in
      let ev1 = Env.find aterm env in
      interpret_comp (compare_interp_val ev1 (to_interpret t1)) op

    | Arith(aterm, msc), Elem(n1, Glob) ->
      let t2 = Term.subst sigma t2 in
      let ev1 = Env.find aterm env in
      interpret_comp (compare_interp_val ev1 (to_interpret t2)) op
    | Elem(p1, Var), Elem(p2, Var) ->
      let t1 = Term.subst sigma t1 in
      let t2 = Term.subst sigma t2 in
      interpret_comp (compare_interp_val (to_interpret t1) (to_interpret t2)) op
    | tt1, Elem(_, SystemProcs) ->
      let t1 = Term.subst sigma tt1 in
      interpret_comp (compare_interp_val (to_interpret t1) (to_interpret t2)) op
    | Elem(_,SystemProcs), tt1 ->
      let t2 = Term.subst sigma tt1 in
      interpret_comp (compare_interp_val (to_interpret t2) (to_interpret t1)) op

    | ProcManip _ , _ ->
      let t2 = Term.subst sigma t2 in
      let pt = add_sub_manip t1 sigma in
      interpret_comp (compare_interp_val pt (to_interpret t2)) op 
      
    | _, ProcManip  _ ->
      let t1 = Term.subst sigma t1 in
      let pt = add_sub_manip t2 sigma in
      interpret_comp (compare_interp_val (to_interpret t1) pt) op
	
    | _ -> assert false
      
let check_reqs reqs env sigma tname=
  SAtom.iter (fun atom ->
    match atom with
      | Comp (t1,op,t2) ->
	if Options.debug_interpreter then 
	  Format.eprintf "Checking requirements, comparing t1 and t2: %a -- %a@." Term.print t1 Term.print t2;
	let b = check_comp t1 t2 env sigma op in
	if b  then ()
	else raise (TopError (FalseReq tname))		
      | True -> ()
      | False ->  raise (TopError (FalseReq tname))
      | Ite _ -> assert false
  ) reqs

let check_switches swts env name sigma  =
  List.fold_left (fun (acc,flag) (sa, t) ->
    let v=
      SAtom.fold (fun atom acc2 ->
	match atom with
	  | Comp(t1, op, t2) ->
	    begin
	      match t1,t2 with
		| Elem(n1,Var), Elem(n2,Var) -> assert false
		| Elem(n1,Var), _ ->
		  let g =
		    try List.assoc n1 sigma with
			Not_found -> assert false 
		  in
		  check_comp (Elem(g, Var)) t2 env sigma op && acc2
		|  _, Elem(n1,Var) ->

		  let g =
		    try List.assoc n1 sigma with
			Not_found -> assert false 
		  in
		  check_comp (Elem(g, Var)) t1 env sigma op && acc2
	        
		| _ ->
		  let b = check_comp t1 t2 env sigma op in
		  b && acc2
	  end 
	  | True -> true && acc2
	  | False -> false && acc2
	  | _ -> assert false		
    ) sa true in
    if v && not flag then
      (Env.add name (to_interpret (Term.subst sigma t) ) env , v)  
    else 
    (acc,flag)  
  ) (env,false) swts 
      
	

let update_vals env assigns sigma =
  List.fold_left (fun acc (name, assign) ->
    let elem = Elem(name, Glob) in
    match assign with
      | UTerm t ->
	begin
	  match t with
	    | Elem (_, Glob) | Access _ ->
	      let v = Env.find (Term.subst sigma t) env in
	      Env.add elem v acc
	    | Arith(t', cs) ->
	      let i_cs = int_of_consts cs in
	      let {value = v; typ = typ} = Env.find elem env in
	      let v' = match v with
		| VInt vi -> VInt (vi + i_cs) |  _ -> assert false in	      
	      Env.add elem {value = v';  typ = typ} acc
	    | Elem(n,Var) -> Env.add elem (to_interpret (Term.subst sigma t)) acc
	      
	    | ProcManip ([t], addsub ) -> let t = Term.subst sigma t in
					Env.add elem (to_interpret (ProcManip([t],addsub))) acc
	    | _ ->
	      
	      Env.add elem (to_interpret (Term.subst sigma t)) acc
	end 
      | UCase t ->
	fst (check_switches t env elem sigma )
  (* (Satom.t * term ) list --> c1 : t1 ...*)
  ) env assigns 

let upd_arr_direct sigma orig upd tname =
  let (ups, upt) = List.hd upd.up_swts in
  let atoms = SAtom.elements ups in
  match atoms with
    | [Atom.Comp(t1, op, Elem(n,Var))] ->
      let elem = Access(tname, [n]) in
      let t = Term.subst sigma elem in
      begin
	match upt with
	  | Elem(_, Glob) | Access _ -> let t2 = Env.find upt orig in
					t, t2
	  | ProcManip ([tpm], addsub) -> let tt = Term.subst sigma tpm in
			   t, (to_interpret (ProcManip([tt],addsub))) 

	    
	  | _ -> t, (to_interpret (Term.subst sigma upt))
      end 
      | _ -> assert false


(*X[k] := case | i = k -> case where you compare generale with proc in args *)
let create_case_proc op accatom g side h all_procs term upd =
  match op with
    | Eq ->			  
      begin   
	let temp = Access(upd.up_arr, [g]) in
	Hashtbl.replace h g true;
	Env.add temp (to_interpret term ) accatom		      		 
      end, true
    | Lt ->
      List.fold_left (fun tacc el ->
	let b = 
	  if side then Hstring.compare g el
	  else Hstring.compare el g in 
	if b = -1 then
	  begin
	    Hashtbl.replace h el true;
	    let temp = Access(upd.up_arr, [el]) in
	    Env.add temp (to_interpret term ) tacc 
	  end
	else tacc 
      ) accatom all_procs, true
    | Le ->
      List.fold_left (fun tacc el ->
	let b = 
	  if side then Hstring.compare g el
	  else Hstring.compare el g in  
	if b = -1 || b = 0 then
	  begin
	    Hashtbl.replace h el true;
	    let temp = Access(upd.up_arr, [el]) in
	    Env.add temp (to_interpret term ) tacc 
	  end
	else tacc 
      ) accatom all_procs, true
    | Neq ->
      List.fold_left (fun tacc el ->			    
	if Hstring.compare g el = 0 then
	  tacc
	else 
	  begin
	    Hashtbl.replace h el true;
	    let temp = Access(upd.up_arr, [el]) in
	    Env.add temp (to_interpret term ) tacc 
	  end
	    
      ) accatom all_procs, true

let check_proc_comparison n1 n2 sigma op accatom upd term h all_procs =
  let g1, fg1 =
    try List.assoc n1 sigma, true
    with Not_found -> Hstring.make "", false
  in
  let g2, fg2 =
    try List.assoc n2 sigma, true
    with Not_found -> Hstring.make "", false
  in
  match fg1, fg2 with
    | false, false -> assert false
    | true, false -> create_case_proc op accatom g1 true h all_procs term upd
    | false, true -> create_case_proc op accatom g2 false h all_procs term upd
    | true, true ->
      begin
	match op with
	  | Eq ->
	    if Hstring.compare g1 g2 = 0 then
	      List.fold_left (fun tacc el ->
		Hashtbl.replace h el true;
		let temp = Access(upd.up_arr, [el]) in
		Env.add temp (to_interpret term ) tacc) accatom all_procs, true
	    else accatom, false
	  | Neq ->
	    if Hstring.compare g1 g2 <> 0 then
	      List.fold_left (fun tacc el ->
		Hashtbl.replace h el true;
		let temp = Access(upd.up_arr, [el]) in
		Env.add temp (to_interpret term ) tacc) accatom all_procs, true
	    else accatom,false
	  | _ -> assert false
	     
      end 
 
let switchy_satoms op g1 g2 sacc =
  match op with
    | Eq ->
      if Hstring.compare g1 g2 = 0 then true && sacc
      else false && sacc 
    | Neq ->
      if Hstring.compare g1 g2 <> 0 then true && sacc
      else false && sacc 
    | Lt ->
      if Hstring.compare g1 g2 = -1 then true && sacc
      else false && sacc 
    | Le ->
      let b = Hstring.compare g1 g2 in
      if  b = -1 || b = 0 then true && sacc
      else false && sacc 

let upd_array_case sigma orig upd tname env =
  let all_procs = Variable.give_procs (Options.get_interpret_procs ()) in 
  (*List.iter (fun x -> Format.eprintf "pre filter: %a@." Hstring.print x) all_procs;*)
  let all_procs = List.filter (fun x ->
    let elem = Elem(x, Var) in
    let v = Env.find elem env in
    v.value = VAlive) all_procs in
  (*List.iter (fun x -> Format.eprintf "Post filter: %a@." Hstring.print x) all_procs;*)
  let swts = upd.up_swts in
  List.fold_left (fun acc proc ->
    let e, _ = 
      List.fold_left (fun (acc2,f) (sa,t) ->
	let t = 
	match t with
	  | Access(n,[pl]) ->
	    begin
	      let pl' =
		try
		  List.assoc pl sigma
		with Not_found -> proc
	      in Env.find (Access(n,[pl'])) env		
	    end
	  | Elem(_, Glob) -> Env.find t env
	  | Elem(np, Var) -> let tt = Variable.subst sigma np in {value = VProc tt; typ = Smt.Type.type_proc} 
	  | ProcManip([pmt], addsub) ->
	    let pmt = Term.subst sigma pmt in
	    to_interpret (ProcManip([pmt],addsub))
	  | _ -> to_interpret t
	in	
      let flag = 
	SAtom.fold (fun atom sacc ->
	  match atom with
	    | Comp (t1,op,t2) ->
	      begin
		match t1,t2 with
		  | Elem(n1,Var), Elem(n2, Var) ->
		  let g1 =
		    try Some (List.assoc n1 sigma)
		    with Not_found -> None
		  in
		  let g2 =
		    try Some (List.assoc n2 sigma)
		    with Not_found -> None
		  in
		  
		  begin
		    match g1, g2 with
		      | None, None -> assert false (*should not happen*)
			
		      | Some gn1, None -> switchy_satoms op gn1 proc sacc  && sacc
					
		      | None, Some gn1 -> switchy_satoms op proc gn1 sacc  && sacc
 
		      | Some gn1, Some gn2 -> switchy_satoms op gn1 gn2 sacc  && sacc		
			
		  end 

		  | Elem(n1,Var), _  ->
		    let g =
		      try List.assoc n1 sigma with
			  Not_found ->  proc
		    in
		    check_comp (Elem(g, Var)) t2 env sigma op  && sacc
		  | _, Elem(n1,Var) ->
		    let g =
		      try List.assoc n1 sigma with
			  Not_found ->  proc
		    in
		    check_comp (Elem(g, Var)) t1 env sigma op  && sacc
		      	    
		  | Access(n1, [pn1]), _ ->
		    let g =
		      try List.assoc pn1 sigma with
			Not_found -> proc
		    in
		    check_comp (Access(n1,[g])) t2 env sigma op  && sacc
		    
		  | _, Access(n1, [pn1]) ->
		    let g =
		      try List.assoc pn1 sigma with
			Not_found -> proc
		    in check_comp t1 (Access(n1,[g])) env sigma op && sacc(*DO THIS FOR MATRIX*)
		  | _ ->
		    (*let t1 = Term.subst sigma t1 in
		    let t2 = Term.subst sigma t2 in*) 
		    check_comp t1 t2 env sigma op && sacc
	    end
	  | True -> true && sacc
	  | False -> false && sacc
	  | Ite _ -> assert false
	    
	) sa true
	  
      in
      if flag && not f then
	let temp = Access(upd.up_arr, [proc]) in
	Env.add temp t acc2, true
      else acc2, f 	
    ) (acc,false) swts
    in e  
  ) env all_procs

let upd_matrix sigma orig upd =
  (*List.iter (fun x -> Format.eprintf "%a@." Hstring.print x) upd.up_arg;*)
  let s = Hstring.view (List.hd upd.up_arg) in
  let s1 = String.sub s 0 1 in
  let flag =  s1 = "_" in
  (*if flag then normal else case construct*)
  match flag with
    | true -> 
      let e, _ = List.fold_left (fun (facc,fflag) (sa,t) ->	
	if not fflag then
	  begin
	    let p1,p2 =
	      SAtom.fold (fun sa acc ->
		Format.eprintf "new fold@.";
		match sa with
		  | Comp (t1,op,t2) ->
		    begin
		      match t1,t2 with		    
			| Elem(n1,Var), Elem(n2,Var) ->
			  begin
			    match acc with
			      | None,None -> Some n2, None
			      | Some _, Some _ -> assert false
			      | None, Some a -> assert false
			      | Some a, None -> Some a, Some n2
			  end 
			| _ -> assert false
		    end
		  | True -> acc 
		  | _ -> assert false
	      ) sa (None,None) 
	    in
	    match p1,p2 with
	      | Some a, Some b ->
		let elem = Term.subst sigma (Access(upd.up_arr, [a;b]))  in	    
		Env.add elem (to_interpret t ) facc, true
	      | Some _, None -> assert false
	      | None, Some _ -> assert false
	      | None, None -> assert false
	  end
	else facc,fflag
	  
      ) (orig,false) upd.up_swts
      in e
      
    | false ->
      let procs = Variable.give_procs (Options.get_interpret_procs ()) in
      List.iter (fun x -> Format.eprintf "pre filter: %a@." Hstring.print x) procs;
      let procs = List.filter (fun x ->
	let elem = Elem(x, Var) in
	let v = Env.find elem orig in
	(v.value = VAlive) ) procs in
      List.iter (fun x -> Format.eprintf "Post filter: %a@." Hstring.print x) procs;
      let all = gen_array_combs upd.up_arr procs in
      (*List.iter (fun x ->
	List.iter (fun y -> Format.eprintf "%a" Hstring.print y) x; Format.eprintf "@.")all;
      *)
      List.fold_left (fun acc procs ->
	let proc1,proc2 =
	  match procs with | [p1;p2] -> p1,p2 | _ -> assert false
	in
	let  e, _ = 
	List.fold_left (fun (acc2, f) (sa,t) ->
	  let flag =
	    SAtom.fold (fun atom sacc ->
	      match atom with
		| Comp (t1,op,t2)->
		  begin
		    match t1, t2 with
		      | Elem(n1, Var), Elem(n2,Var) ->
			let proc1, proc2 = 
			  if Hstring.compare n1 (List.hd upd.up_arg) = 0
			  then proc1, proc2
			  else proc2, proc1 in 
			let g1, gf1 =
			  try Some (List.assoc n1 sigma), true
			  with Not_found -> None, false
			in
			let g2, gf2 =
			  try Some (List.assoc n2 sigma), true
			  with Not_found -> None, false
			in
			begin
			  match g1, g2 with
			    | None, None ->
	        	      switchy_satoms op proc1 proc2 sacc			  
			    | Some gn1, None ->
			      switchy_satoms op gn1 proc2 sacc
			    | None, Some gn1 ->
			      switchy_satoms op proc1 gn1 sacc
			    | Some gn1, Some gn2 ->
			      switchy_satoms op gn1 gn2 sacc

			end 
		      | _ -> assert false (*other to elem*) (*TODO ADD OTHER COMPS*)			
			
		  end 		  
		| True -> true && sacc
		| False -> false && sacc
		| Ite _ -> assert false
	    ) sa true

	  in if flag && not f then
	      let temp = Access(upd.up_arr, procs)
	      in Env.add temp (to_interpret t ) acc2, true
	    else acc2, f
	) (acc,false) upd.up_swts
	in e  
      )orig all

      
      
      
    
let update_arrs sigma orig acc upds =
  List.fold_left (fun acc1 upd ->
    let name = upd.up_arr in
    (*List.iter (fun x -> Format.eprintf "arg %a@." Hstring.print x) upd.up_arg;*)
    if List.length upd.up_arg = 1 then
      let s = Hstring.view (List.hd upd.up_arg) in
      let s1 = String.sub s 0 1 in
      if s1 = "_" then 
      let t, v = upd_arr_direct sigma orig upd name in
      Env.add t v acc1
      else
	let e = (*upd_arr_case*) upd_array_case sigma orig upd name acc1 in
	(*Env.add t v acc1 *) e
    else upd_matrix sigma orig upd 
    
  ) acc upds

      
let uguard env sigma args tr_args = function
  | [] -> [SAtom.empty]
  | [j, dnf] ->
    let uargs = List.filter (fun a -> not (Hstring.list_mem a tr_args)) args in
    let uargs =
      List.fold_left (fun acc proc ->
	let elem = Elem(proc, Var) in
	let v = Env.find elem env in
	match v.value with
	  | VAlive -> proc::acc
	  | VSuspended -> acc
	  | _ -> acc ) [] uargs 
    in 
      List.fold_left 
	(fun lureq z ->
	   let m = List.map (SAtom.subst ((j, z)::sigma)) dnf in
	   List.fold_left 
	     (fun acc sa -> 
		(List.map (fun zy-> SAtom.union zy sa) m) @ acc ) [] lureq
	)
	[SAtom.empty]
	uargs
  | _ -> assert false

let map_atoms a sigma =
  match a with
    | Atom.Comp(t1,op, t2) -> Atom.Comp(Term.subst sigma t1, op, Term.subst sigma t2)
    | Ite _ -> assert false
    | a -> a
    

let upd_non_dets env nondets =
  let proc = Hstring.make "proc" in
  List.fold_left (fun acc el ->
    Env.add (Elem(el, Glob)) {value = random_value proc; typ = proc} acc
  ) env nondets

let wait_unlock lockq lock_elem env =
  let q = LockQueues.find lock_elem lockq in
  if Queue.is_empty q then
    Env.add lock_elem {value = VLock(false,None); typ = ty_lock} env,
    lockq
  else
    let new_proc = Queue.pop q in
    let nv =
      Env.add lock_elem {value = VLock(true, Some new_proc); typ = ty_proc} env
    in
    let nv = Env.add new_proc {value = VAlive; typ = ty_proc} nv in
    let lq = LockQueues.add lock_elem q lockq in nv,lq   
    
let update_locks_unlocks sigma env new_env tr lock_queue cond_sets semaphores=
  let locks = tr.tr_locks in
  let unlocks = tr.tr_unlocks in
  let wait = tr.tr_wait in
  let notify = tr.tr_notify in
  let notifyall = tr.tr_notifyall in 
  match locks,unlocks, wait,notify, notifyall with
    | [], [], [], [], [] -> new_env, lock_queue, cond_sets, semaphores
    | [(lockp)], [], [], [], [] ->     
      begin
	match lockp with
	  | VarLock(lock_elem,p) ->
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env  in
	    begin	      
	     match v.value  with
		| VLock(b, po) ->
		  let term = Elem(Variable.subst sigma p, Var) in 
		  if not b then
		    begin
		      (Env.add lock_elem
			 { value = VLock(true, Some term); typ = v.typ } new_env),
		      lock_queue,
		      cond_sets, semaphores
		    end		
		  else
		    begin
		      if po = None then assert false; (*TODO ERROR*)
		      (*if is_condition v.typ then
			deal_wait true lockp sigma env new_env tr lock_queue cond_sets else*)
		      let q = LockQueues.find lock_elem lock_queue in
		      Queue.push term q;
		      let lock_queue = LockQueues.add lock_elem q lock_queue in
		      (Env.add term {value = VSuspended; typ = ty_proc} new_env),
		      lock_queue,
		      cond_sets, semaphores
		    end
		| VRLock(b,po,i) ->
		  let term = Elem(Variable.subst sigma p, Var) in
		  if not b then
		    (Env.add lock_elem
		       { value = VRLock(true, Some term, 1); typ = v.typ } new_env),
		    lock_queue,
		    cond_sets, semaphores
		  else
		    begin
		      match po with
			| None -> assert false
			| Some p ->
			  let q = LockQueues.find lock_elem lock_queue in

			  if Term.compare p term = 0 then
			    
			    (Env.add lock_elem {value = VRLock(true, Some p,i+1); typ = v.typ} new_env), lock_queue, cond_sets, semaphores

			  else
			    begin
			      Queue.push term q;
			      let lock_queue = LockQueues.add lock_elem q lock_queue in
			      (Env.add term {value = VSuspended; typ = ty_proc} new_env), lock_queue, cond_sets, semaphores
			    end
			    
		    end
		| VSemaphore i ->
		  let term = Elem(Variable.subst sigma p, Var) in 

		  if i > 0 then
		    (Env.add lock_elem { value = VSemaphore(i-1); typ = v.typ} new_env), lock_queue, cond_sets, semaphores
		  else
		    let sl = Semaphores.find lock_elem semaphores in
		    let sema = Semaphores.add lock_elem (term::sl) semaphores in
		    (Env.add term {value = VSuspended; typ = ty_proc} new_env), lock_queue, cond_sets, sema
   		| VGlob _ -> assert false
		| VProc _ -> assert false
		| VInt _ -> assert false
		| VReal _ -> assert false
		| VConstr _ -> assert false
		| VAccess _ -> assert false
		| VAlive -> assert false
		| _ -> assert false
	     
	    end
      
       
      end
      
    | [], [unlock], [], [], []  ->
      begin
	match unlock with
	  | VarLock(lock_elem,p) ->
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env in
	    
	    let p_ask = Elem(Variable.subst sigma p, Var) in	     
	    begin
	      match v.value with
		| VLock(b,po) ->
		  if not b then new_env, lock_queue, cond_sets, semaphores
		  else
		    begin
		      match po with
			| None -> assert false
			| Some proc -> 
			  if Term.compare p_ask proc <> 0
			  then
			    let () = Format.eprintf
			      "@{<b>@{<fg_magenta>WARNING@}@}: Process %a cannot unlock %a's lock, release not applied@." Term.print p_ask Term.print proc in
			  new_env, lock_queue, cond_sets, semaphores
			  (*raise (TopError (CantUnlockOther(p_ask,proc)))*)
			  else 
			    begin
			      let q = LockQueues.find lock_elem lock_queue
			      in
			      if Queue.is_empty q then
				Env.add lock_elem {value = VLock(false,None); typ = v.typ} new_env,
				lock_queue, cond_sets, semaphores
			      else
				let new_proc = Queue.pop q in
				let nv =
				  Env.add
				    lock_elem {value = VLock(true, Some new_proc); typ = v.typ}
				    new_env
				in
				let nv = Env.add new_proc {value = VAlive; typ = ty_proc} nv in
				let lq = LockQueues.add lock_elem q lock_queue in
				nv,lq, cond_sets, semaphores
			    end 
			  
		    end
		| VRLock(b,po,i) ->
		  if not b then new_env, lock_queue, cond_sets, semaphores
		  else
		    begin
		      match po with
			| None -> assert false
			| Some proc ->
			  if Term.compare p_ask proc <> 0
			  then
			    let () = Format.eprintf
			      "@{<b>@{<fg_magenta>WARNING@}@}: Process %a cannot unlock %a's lock, release not applied@." Term.print p_ask Term.print proc in
			    new_env, lock_queue, cond_sets, semaphores




			  (*raise (TopError (CantUnlockOther(p_ask,proc)));*)
			  else
			    begin
			  let q = LockQueues.find lock_elem lock_queue
			  in
			  if i = 1 then
			    if Queue.is_empty q then
			      Env.add lock_elem {value = VRLock(false,None,0); typ = v.typ} new_env,lock_queue, cond_sets, semaphores
			    else
			      let new_proc = Queue.pop q in
			      let nv =
				Env.add
				  lock_elem {value = VRLock(true, Some new_proc,1); typ = v.typ}
				  new_env
			      in
			      let nv = Env.add new_proc {value = VAlive; typ = ty_proc} nv in
			      let lq = LockQueues.add lock_elem q lock_queue in
			      nv,lq, cond_sets, semaphores
			  else
			    Env.add lock_elem {value = VRLock(true, Some proc, i-1); typ = v.typ} new_env,
			    lock_queue , cond_sets, semaphores

		      end
		    end

		| VSemaphore i ->
		  let sl =  Semaphores.find lock_elem semaphores in
		  if sl = [] then
		    (Env.add lock_elem { value = VSemaphore(i+1); typ = v.typ} new_env), lock_queue, cond_sets, semaphores
		  else
		    let wakeup = List.hd sl in 
		    let sema = Semaphores.add lock_elem (List.tl sl) semaphores in
		    (Env.add wakeup {value = VAlive; typ = ty_proc} new_env), lock_queue, cond_sets, sema
		  
		| _ -> assert false
		  		
	    end 
	    
      end
    | [], [], [wait], [], [] -> (*deal_wait false wait sigma env new_env tr lock_queue cond_sets*)    
     begin
	match wait with
	  | VarLock(lock_elem, p) ->
	    let term = Elem(Variable.subst sigma p, Var) in
	    let term_value = Env.find term env in 
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env in
	    begin
	      match v.value with
		| VLock(b,po) ->
		  begin
		    match po with
		      | None ->
			if b then assert false
			else
			  begin
			    match term_value.value with
			      | VSleep i -> if i > 0 then
				  (Env.add term {value = VSleep(i+1); typ = ty_proc} new_env),
				lock_queue,
				cond_sets,
				semaphores
				else 
				  raise (TopError (CantWaitNeverLock (term, lock_elem)))
			      | VSuspended -> raise (TopError (SuspendedProc term))
			      | VAlive ->  raise (TopError (CantWaitNeverLock (term, lock_elem)))
			      | _ -> assert false
			  end 
		      | Some pr ->
			if not b then assert false
			else
			  begin
			    if Term.compare pr term = 0 then
			      let clist = Conditions.find lock_elem cond_sets in
			      let clist = term::clist in
			      let nv, lq = wait_unlock lock_queue lock_elem new_env in
			      (Env.add term {value = VSleep 1; typ = ty_proc} nv),
			      lq,
			      Conditions.add lock_elem clist cond_sets,
			      semaphores
			    else
			      begin
				match term_value.value with
				  | VSleep i -> if i > 0 then
				      (Env.add term {value = VSleep(i+1); typ = ty_proc} new_env),
				    lock_queue,
				    cond_sets,
				    semaphores
				    else 
				      raise (TopError (CantWaitNeverLock (term, lock_elem)))
				  | VSuspended -> raise (TopError (SuspendedProc term))
				  | VAlive ->  raise (TopError (CantWaitNeverLock (term, lock_elem)))
				  | _ -> 
				    assert false
			      end 
			      
			  end 
			
		  end
		  
		| _ -> assert false
	    end 
	
      end 
    | [], [], [], [notify], [] ->
      begin
	match notify with
	  | VarLock(lock_elem,p) ->
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env in
	    let p_ask = Elem(Variable.subst sigma p, Var) in
	    begin
	      match v.value with
		| VLock(b,po) ->
		  if not b then raise (TopError UnlockedNotify);
		  begin
		    match po with
		      | None -> assert false
		      | Some pr ->
			if Term.compare pr p_ask <> 0 then
			(*raise (TopError (CantNotifyNotMine(p_ask, lock_elem)));*)
			  let() =
			    Format.eprintf
			      "Process %a can't notify: lock %a does not belong to %a@."
			      Term.print p_ask Term.print lock_elem Term.print p_ask in
			new_env, lock_queue, cond_sets,	semaphores
			else
			  begin
			    let waiting = Conditions.find lock_elem cond_sets in
			    if waiting = [] then new_env, lock_queue, cond_sets, semaphores
			    else
			      let cond_sets =
				Conditions.add lock_elem (List.tl waiting) cond_sets in
			      let q = LockQueues.find lock_elem lock_queue in
			      
			      let () = Queue.push (List.hd waiting) q in
			      let nv = Env.add (List.hd waiting) { value = VSuspended; typ = ty_proc} new_env in
			      let lq = LockQueues.add lock_elem q lock_queue
			      in nv,lq,cond_sets, semaphores
			  end 
			    
			
		  
			  
			
		  end 
		| _ -> assert false		    
	    end
      end
	
    | [], [], [], [], [notifyall] ->
      begin
	match notifyall with
	  | VarLock(lock_elem,p) ->
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env in
	    let p_ask = Elem(Variable.subst sigma p, Var) in
	    begin
	      match v.value with
		| VLock(b,po) ->
		  if not b then raise (TopError UnlockedNotify);
		  begin
		    match po with
		      | None -> assert false
		      | Some pr ->
			if Term.compare pr p_ask <> 0 then
			(*raise (TopError (CantNotifyNotMine(p_ask, lock_elem)));*)
			  let() =
			    Format.eprintf
			      "Process %a can't notify: lock %a does not belong to %a@."
			      Term.print p_ask Term.print lock_elem Term.print p_ask in
			new_env, lock_queue, cond_sets,	semaphores
			else
			  begin
			    let waiting = Conditions.find lock_elem cond_sets in
			    if waiting = [] then new_env, lock_queue, cond_sets, semaphores
			    else
			      let cond_sets =
				Conditions.add lock_elem [] cond_sets in
			      let q = LockQueues.find lock_elem lock_queue in
			      let nv =
				List.fold_left (fun acc el ->
				  Env.add el {value = VSuspended; typ = ty_proc } acc) new_env waiting
			      in  
			      let () = List.iter (fun el -> Queue.push el q) waiting in
			      let lq = LockQueues.add lock_elem q lock_queue
			      in nv,lq,cond_sets, semaphores
			  end
		  end 
		| _ -> assert false		    
	    end
      end


      
    | _ -> assert false
  
let check_actor_suspension sigma env actor =
  match actor with
    | None -> ()
    | Some p -> let elem = Term.subst sigma (Elem(p, Var)) in
		let v = Env.find elem env in
		begin
		match v.value with
		  | VAlive -> ()
		  | VSuspended -> raise (TopError (SuspendedProc elem))
		  | VSleep _ -> raise (TopError (SleepingProc elem))
		  | _ -> assert false
		end
      
let check_suspension sigma env =
  List.iter (fun (_, el) ->
    let elem = Elem(el, Var) in
    let v = Env.find elem env in
    match v.value with
      | VAlive -> ()
      | VSuspended -> raise (TopError (SuspendedProc elem))
      | VSleep _ -> raise (TopError (SleepingProc elem))
      | _ -> assert false) sigma
    
let apply_transition args trname trans (env,lock_queue,cond_sets, semaphores) =
  let tr = Trans.find trname trans in
  let arg_length = List.length tr.tr_args in
  if List.length args <> arg_length then
    raise (TopError (WrongArgs (trname,arg_length)));
  let sigma = Variable.build_subst tr.tr_args args in
  check_actor_suspension sigma env tr.tr_process;
  let () = check_reqs tr.tr_reqs env sigma trname in
  let procs = Variable.give_procs (Options.get_interpret_procs ()) in
  let trargs = List.map (fun x -> Variable.subst sigma x) tr.tr_args in
  let ureqs = uguard env sigma procs trargs tr.tr_ureq in
  let () = List.iter (fun u -> check_reqs u env sigma trname) ureqs in

  let nv = update_vals env tr.tr_assigns sigma in
  let nv = update_arrs sigma env nv tr.tr_upds in
  let nv, lockq,cond_sets, semaphores = update_locks_unlocks sigma env nv tr lock_queue cond_sets semaphores in 
  upd_non_dets nv tr.tr_nondets,lockq,cond_sets, semaphores
      
let check_duplicates l =
  let h = Hashtbl.create( List.length l) in
  List.iter (fun x ->
    try
      let b = Hashtbl.find h x in
      if b then raise (TopError DupProcs)
    with Not_found ->  Hashtbl.add h x true
  ) l

let all_possible_transitions (env,_,_,_) trans all_procs flag=
  Trans.fold (fun x el acc ->
    let name = el.tr_name in 
    let args = el.tr_args in
    let num_args = List.length args in
    let tr_procs = all_arrange num_args all_procs in
    if tr_procs = [] then
      begin
	try 
	  let sigma = Variable.build_subst args [] in
	  check_actor_suspension sigma env el.tr_process;
	  check_reqs el.tr_reqs env sigma name;
	  let trargs = List.map (fun x -> Variable.subst sigma x) args in
	  let ureqs = uguard env sigma all_procs trargs el.tr_ureq in
	  List.iter (fun u -> check_reqs u env sigma name) ureqs;
	  (el,[])::acc
	with
	  | TopError _ -> acc
	  | _ -> assert false
      end
    else
      begin
	List.fold_left (fun acc_t procs ->
	  let sigma = Variable.build_subst args procs in
	  try
	    check_actor_suspension sigma env el.tr_process;
	    check_reqs el.tr_reqs env sigma name;
	    let trargs = List.map (fun x -> Variable.subst sigma x) args in
	    let ureqs = uguard env sigma all_procs trargs el.tr_ureq in
	    List.iter (fun u -> check_reqs u env sigma name) ureqs;	  
	    (el, procs)::acc_t
	  with
	    | TopError _ -> acc_t
	    | Sys.Break ->
	      if flag
	      then
		raise Sys.Break
	      else raise Exit
	    | s -> let e = Printexc.to_string s in Format.printf "%s@." e; assert false      
	) acc tr_procs
      end 
  ) trans []
    

let execute_random fmt glob_env trans all_procs unsafe =
  Sys.catch_break true;
  let q = Queue.create () in
  Random.self_init ();
  let running_env = ref glob_env in
  let transitions = ref (Array.of_list (all_possible_transitions glob_env trans all_procs false)) in 
  let running = ref true in
  while !running do
    try
      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (apply,apply_procs) = !transitions.(rand) in
      Queue.push (apply,apply_procs) q;
      running_env := apply_transition apply_procs apply.tr_name trans !running_env;
      transitions := Array.of_list (all_possible_transitions !running_env trans all_procs true);
      check_unsafe !running_env unsafe
    with
      | TopError Deadlock -> Sys.catch_break false;
	Format.fprintf fmt
	"@{<b>@{<fg_red>WARNING@}@}: Deadlock reached@."; running := false
      | TopError Unsafe ->
	Sys.catch_break false;
	Format.fprintf fmt
	"@{<b>@{<fg_red>WARNING@}@}: Unsafe state reached. Do you wish to continue? (y/n)@.";
	begin
	  let rec decide () =
	    let inp = read_line () in
	    match inp with
	      | "y" -> Sys.catch_break true
	      | "n" -> running := false
	      | _ -> Format.fprintf fmt "Invalid input@."; decide ()
	  in decide ()
	end 
      | Stdlib.Sys.Break -> Sys.catch_break false; running := false
      | TopError InputError -> assert false
      | TopError NoTransition _ -> assert false
      | TopError WrongArgs _ -> assert false
      | TopError NoVar _ -> assert false
      | TopError TooManyProcs -> assert false
      | TopError FalseReq _ -> assert false
      | TopError ConflictInit _ -> assert false
      | TopError UnEqConstr _ -> assert false
      | TopError CannotProc -> assert false
      | TopError DupProcs -> assert false
      | TopError Reached -> assert false
      | TopError BadType _ -> assert false
      | TopError BadInit -> assert false
      | TopError SuspendedProc _ -> assert false
      | TopError SleepingProc _ -> assert false
      | TopError CantUnlockOther _ -> Format.eprintf "hh@.";running := false
      | TopError CantWaitNeverLock _ -> assert false
      | TopError UnlockedNotify -> assert false
      | TopError CantNotifyNotMine _ -> assert false
      | s -> Sys.catch_break false;
	let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
	assert false
  done;
    q, !running_env


  
    
let generate_process (env, locks, conds, semaphores) number tsys=
  let arrays = tsys.t_arrays in 
  let new_num = Options.get_interpret_procs () + 1 in 
  let () = Options.set_interpret_procs new_num in
  let new_proc = Hstring.make ("#"^(string_of_int new_num)) in
  let env =
    Env.add (Elem(new_proc, Var)) {value = VAlive; typ = ty_proc} env
  in
  let env = 
  List.fold_left (fun acc el ->
    let _, ty = Smt.Symbol.type_of el in 
    Env.add (Access(el, [new_proc])) {value = random_value ty; typ = ty } acc) env arrays
  in 
  env,locks,conds, semaphores

    
let setup_env tsys sys =
  let fmt = Format.std_formatter  in

  (*generate X distinc procs*)
  let num_procs = Options.get_interpret_procs () in
  let procs = Variable.give_procs num_procs in

  (*all terms for the procs, i.e generate instantiated array terms*)
  (* var X[proc]: bool --> X[#1], X[#2] ...  *)
  let var_terms = Forward.all_var_terms procs tsys in
  let const_list = List.map (fun x -> Elem(x, Glob)) tsys.t_consts in
  let var_terms = Term.Set.union var_terms (Term.Set.of_list const_list) in 
  sys_procs := Options.get_interpret_procs (); 
 
  let orig_env,lock_queue, cond_sets, semaphores =
    Term.Set.fold ( fun x (acc,acc_lock, cond_acc, sem_acc) ->
      match x with
	| Elem (n1, Glob) ->
	  let _,ty = Smt.Symbol.type_of n1 in
	  if is_lock ty || is_rlock ty then
	    (Env.add x throwaway acc ,
	     LockQueues.add x (Queue.create ()) acc_lock,
	    cond_acc, sem_acc)
	  else
	    if is_condition ty then
	      Env.add x throwaway acc , LockQueues.add x (Queue.create ()) acc_lock, Conditions.add x [] cond_acc, sem_acc
	    else
	      if is_semaphore ty then
		Env.add x throwaway acc, acc_lock, cond_acc, Semaphores.add x [] sem_acc
	      else 
		(Env.add x throwaway acc , acc_lock, cond_acc, sem_acc)
	| Access(arr,arps) ->
	  let _,ty = Smt.Symbol.type_of arr in
	  if is_lock ty then
	    (Env.add x throwaway acc , LockQueues.add x (Queue.create ()) acc_lock, cond_acc, sem_acc)
	  else
	    if is_condition ty then
	      Env.add x throwaway acc , LockQueues.add x (Queue.create ()) acc_lock, Conditions.add x [] cond_acc, sem_acc
	    else
	      if is_semaphore ty then
		Env.add x throwaway acc, acc_lock, cond_acc, Semaphores.add x [] sem_acc
	      else 
		(Env.add x throwaway acc , acc_lock, cond_acc, sem_acc)
	       
	| _ -> Env.add x throwaway acc , acc_lock, cond_acc, sem_acc
    ) var_terms (Env.empty, LockQueues.empty, Conditions.empty, Semaphores.empty)
  in

  if Options.debug_interpreter then
    begin
      Format.eprintf "Very first environment:@.";
      print_env fmt orig_env
    end;
    
  let env = init_vals orig_env tsys.t_init in

  if Options.debug_interpreter then
    begin
    Format.eprintf "First initialized environment: @.";
    print_env fmt env
    end;
  
    let env_final =
      Env.mapi (fun k x ->
	if Term.compare x throwaway = 0 then
	  begin
	    match k with 
	      | Elem(n,_) | Access(n,_) -> 
		let _, ty = Smt.Symbol.type_of n in
	    {value = random_value ty; typ = ty }
	  |  _ -> assert false	
	end
      else
	begin
	  match k with
	    | Elem(n, _) | Access(n, _) ->
	      let _, ty = Smt.Symbol.type_of n in
	      if is_semaphore ty then
		  {value = semaphore_init x; typ = ty}
	      else
		{value = cub_to_val x ; typ = ty }
	    | _ -> assert false

	end
    ) env in
  let env_final =
    Env.mapi (fun k x ->
      (*let ty = Smt.Symbol.type_of k in *)
      match x.value with
	| VArith ta -> let v = eval_arith ta env_final x.typ in
		       {value =  v; typ = x.typ}
	| _ -> x ) env_final in
  
  let env_final =
    List.fold_left (fun acc x ->
      Env.add (Elem(x, Var)) {value = VAlive; typ = ty_proc} acc
  ) env_final procs
  in

  let transitions =
    List.fold_left ( fun acc t ->    
      Trans.add t.tr_name t acc ) Trans.empty sys.trans in

  let global_env = ref (env_final,lock_queue, cond_sets, semaphores) in 
  
  ignore (Sys.command "clear");
  while !interpret_bool do
    try
      flush stdout; Format.printf "> %!";
      let inp = read_line () in	  
      let tts = Parser.toplevel Lexer.token (Lexing.from_string inp) in
      (match tts with
	| TopExec -> let ap, g =  execute_random fmt !global_env transitions procs sys.unsafe
		     in
		     global_env := g;
		     print_applied_trans fmt ap
	| TopTransition tl ->
	  let temp =
	    try
	      List.fold_left (fun acc t ->
		match t with
		  | (n, []) -> apply_transition [] n transitions acc
		  | (n,l) ->		    
		    check_duplicates l;
		    apply_transition l n transitions acc ) !global_env tl
	    with
	      | TopError (FalseReq fr) ->
		Format.printf "%a@." top_report (FalseReq fr); !global_env in
	  global_env := temp
	| TopShowEnv -> print_interpret_env fmt !global_env 
	| TopHelp -> print_help fmt
	| TopClear -> ignore (Sys.command "clear")
	| TopTest h ->	  	  
	  let l = all_possible_transitions !global_env transitions procs false in
		       if l = [] then raise (TopError Deadlock)
		       else
			 print_poss_trans fmt l
	| TopUnsafe -> check_unsafe !global_env sys.unsafe 
	| TopRestart ->
	  print_interpret_env fmt (env_final, lock_queue, cond_sets, semaphores);
	  global_env := env_final,lock_queue, cond_sets, semaphores;
	  print_interpret_env fmt !global_env
	| TopGenProc -> global_env := generate_process !global_env num_procs tsys
	| TopKillProc op -> assert false
	| TopAssign(name,n, tt) ->
	  (*TO DO FOR CONSTRUCTORS: check that it belongs to type*)
	  try
	    let e, lq, cond,sem = !global_env in
	    let v = Env.find n e in
	    let v1 =
	      try Env.find tt e
	      with Not_found -> to_interpret tt
	    in 
	    if Hstring.compare v.typ v1.typ <> 0 then raise (TopError (BadType (v.typ, v1.typ)))
	    else
	      let v,l,c,s = !global_env in 
	      global_env := Env.add n v1 v, l, c,s
	  with
	      Not_found ->
		  raise (TopError (NoVar name))
	  
      );
      
    with
      | TopError e -> Sys.catch_break false;Format.printf "%a@." top_report e
      | End_of_file  -> Sys.catch_break false;interpret_bool := false
      | s ->  Sys.catch_break false; let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError)
      
  done 
  
