open Ast
open Types
open Interpret_errors
open Interpret_types
open OcamlCanvas.V1



let interpret_bool = ref true
let step_flag = ref 1
let btracks = ref []
let deadlock = ref false

  
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

let fresh_back = 
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

let give_pre (env,_,_,_) tt=
  let procs = Variable.give_procs (Options.get_interpret_procs ()) in
  let v = Env.fold (fun key {value = el} acc ->
    match el with
      | VGlob el -> SAtom.add (Comp(key, Eq, Elem(el, Glob))) acc 
      (*| VProc el -> SAtom.add (Comp(key, Eq, Elem(el, Var))) acc*)
      | VConstr el -> SAtom.add (Comp(key, Eq, Elem(el, Constr))) acc
      | VAccess(el,vl) -> SAtom.add (Comp(key, Eq, Access(el, vl))) acc
      | _-> acc   
  ) env SAtom.empty
  in
  let cube = Cube.create procs v in
  let node = Node.create cube in 
  let a, _ = Pre.pre_image tt node in
  List.iter (fun x -> Format.printf "%a@." Node.print x) a

    


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
  (*let all_procs = List.filter (fun x ->
    let elem = Elem(x, Var) in
    let v = Env.find elem env in
    v.value = VAlive) all_procs in*)
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
      (*let procs = List.filter (fun x ->
	let elem = Elem(x, Var) in
	let v = Env.find elem orig in
	(v.value = VAlive) ) procs in*)
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
    (*let uargs =
      List.fold_left (fun acc proc ->
	let elem = Elem(proc, Var) in
	let v = Env.find elem env in
	match v.value with
	  | VAlive -> proc::acc
	  | VSuspended -> acc
	  | _ -> acc ) [] uargs 
    in *)
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
  if PersistentQueue.is_empty q then
    Env.add lock_elem {value = VLock(false,None); typ = ty_lock} env,
    lockq
  else
    let new_proc, rem_queue = PersistentQueue.pop q in
    let nv =
      Env.add lock_elem {value = VLock(true, Some new_proc); typ = ty_proc} env
    in
    let nv = Env.add new_proc {value = VAlive; typ = ty_proc} nv in
    let lq = LockQueues.add lock_elem rem_queue lockq in nv,lq   
    
let update_locks_unlocks sigma env new_env tr lock_queue cond_sets semaphores=
  let locks = tr.tr_locks in
  (*let unlocks = tr.tr_unlocks in
  let wait = tr.tr_wait in
  let notify = tr.tr_notify in
  let notifyall = tr.tr_notifyall in*) 
  match locks with
    | [] -> new_env, lock_queue, cond_sets, semaphores
    | [Lock lockp] ->
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
		      let new_queue =  PersistentQueue.push term q in
		      let lock_queue = LockQueues.add lock_elem new_queue lock_queue in
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
			      let new_queue = PersistentQueue.push term q in
			      let lock_queue = LockQueues.add lock_elem new_queue lock_queue in
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
      
    | [Unlock unlock]  ->
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
			      if PersistentQueue.is_empty q then
				Env.add lock_elem {value = VLock(false,None); typ = v.typ} new_env,
				lock_queue, cond_sets, semaphores
			      else
				let new_proc, rem_procs = PersistentQueue.pop q in
				let nv =
				  Env.add
				    lock_elem {value = VLock(true, Some new_proc); typ = v.typ}
				    new_env
				in
				let nv = Env.add new_proc {value = VAlive; typ = ty_proc} nv in
				let lq = LockQueues.add lock_elem rem_procs lock_queue in
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
			    if PersistentQueue.is_empty q then
			      Env.add lock_elem {value = VRLock(false,None,0); typ = v.typ} new_env,lock_queue, cond_sets, semaphores
			    else
			      let new_proc, rem_procs = PersistentQueue.pop q in
			      let nv =
				Env.add
				  lock_elem {value = VRLock(true, Some new_proc,1); typ = v.typ}
				  new_env
			      in
			      let nv = Env.add new_proc {value = VAlive; typ = ty_proc} nv in
			      let lq = LockQueues.add lock_elem rem_procs lock_queue in
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
    | [Wait wait] -> (*deal_wait false wait sigma env new_env tr lock_queue cond_sets*)    
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
    | [Notify notify] ->
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
			      
			      let new_queue = PersistentQueue.push (List.hd waiting) q in
			      let nv = Env.add (List.hd waiting) { value = VSuspended; typ = ty_proc} new_env in
			      let lq = LockQueues.add lock_elem new_queue lock_queue
			      in nv,lq,cond_sets, semaphores
			  end 
			    
			
		  
			  
			
		  end 
		| _ -> assert false		    
	    end
      end
	
    | [NotifyAll notifyall] ->
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
			      let new_queue = List.fold_left (fun acc el -> PersistentQueue.push el acc) q waiting in
			      let lq = LockQueues.add lock_elem new_queue lock_queue
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



let explain_reqs reqs env sigma tname args=
  SAtom.fold (fun atom acc ->
    match atom with
      | Comp (t1,op,t2) ->
	if Options.debug_interpreter then 
	  Format.eprintf "Checking explain requirements, comparing t1 and t2: %a -- %a@." Term.print t1 Term.print t2;
	let b = check_comp t1 t2 env sigma op in
	if b then acc
	else SAtom.add (Comp(Term.subst sigma t1, op, Term.subst sigma t2)) acc	
      | True -> acc
      | False ->  SAtom.add atom acc 
      | Ite _ -> assert false
  ) reqs SAtom.empty

    
let explain args trname trans (env,lock_queue,cond_sets, semaphores) =
  let tr = Trans.find trname trans in
  let arg_length = List.length tr.tr_args in
  if List.length args <> arg_length then
    raise (TopError (WrongArgs (trname,arg_length)));
  let sigma = Variable.build_subst tr.tr_args args in
  try
    check_actor_suspension sigma env tr.tr_process;
    let satom = explain_reqs tr.tr_reqs env sigma trname args in
    let procs = Variable.give_procs (Options.get_interpret_procs ()) in
    let trargs = List.map (fun x -> Variable.subst sigma x) tr.tr_args in
    let ureqs = uguard env sigma procs trargs tr.tr_ureq in
    let final =
      List.fold_left (fun acc u ->
	let r = explain_reqs u env sigma trname args in
      SAtom.union r acc ) satom ureqs
    in
    if SAtom.is_empty final then
      Format.printf "Transition %a(%a) NOT blocked@." Hstring.print trname Variable.print_vars args
    else
      begin
	Format.printf "Transition %a(%a) blocked because following reqs are false:@." Hstring.print trname Variable.print_vars args; 
	SAtom.iter (fun atom ->
      Format.printf "\t%a@." Atom.print atom) final
      end
  with
    | TopError SuspendedProc pp -> Format.printf "Transition %a(%a) blocked due to suspended %a@." Hstring.print trname Variable.print_vars args Term.print pp
    | TopError SleepingProc pp -> Format.printf "Transition %a(%a) blocked due to sleeping %a@." Hstring.print trname Variable.print_vars args Term.print pp
       
      
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
	  | Stdlib.Sys.Break ->
	    if flag
	    then
	      raise (TopError StopExecution)
	    else raise Exit
	  | s -> let e = Printexc.to_string s in Format.printf "%s @." e;
		 assert false
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
		raise (TopError StopExecution)
	      else  raise Exit
	    | s -> let e = Printexc.to_string s in Format.printf "%s@." e; assert false      
	) acc tr_procs
      end 
  ) trans []
    

let print_header f name=
  let f = Format.formatter_of_out_channel f in 
  Format.fprintf f "***Tested states***\n\
                    Filename: %s\n\
                    Number of procs: %d\n\
                    *******************\n@." name (Options.get_interpret_procs())




let print_backtrace env =
  Backtrack.iter (fun num (name, procs, env) ->
    Format.printf
      "Step in execution: %d\n Applied transition: %a(%a)\n Resulting Environment\n%a"
      num Hstring.print name Variable.print_vars procs print_debug_env env) env
    
let rec exp n =
  if n = 0 then Format.printf "@." else
    begin 
      Format.printf "\r%d" n; exp (n-1)
    end 

    
let print_val fmt v =
  match v with
    | VInt i -> Format.fprintf fmt "%d" i
    | VReal r -> Format.fprintf fmt "%f" r
    | VBool b -> Format.fprintf fmt "%b" b
    | VConstr el | VGlob el  -> Format.fprintf fmt "%a" Hstring.print el
    | VProc i -> Format.fprintf fmt "%a" Hstring.print i
    | VLock(b, vo) ->
      if b then
	match vo with
	  | None -> assert false
	  | Some p -> Format.fprintf fmt "locked by process %a" Term.print p
      else
	Format.fprintf fmt "unlocked"
    | VAlive -> Format.fprintf fmt "process active"
    | VSuspended -> Format.fprintf fmt "process suspended"
    | VSleep _ -> Format.fprintf fmt "process asleep"
    | VRLock (b,po,i) ->
      if b then
	 match po with
	   | None -> assert false
	   | Some p -> Format.fprintf fmt "locked by process %a %d time(s)" Term.print p i
      else
	Format.fprintf fmt "unlocked"
    | VSemaphore i -> Format.fprintf fmt "%d" i
    | UNDEF -> Format.fprintf fmt "%s" "UNDEF"
    | VAccess(l,t) -> Format.fprintf fmt "%a[%a]" Hstring.print l (Hstring.print_list ", ") t
    | VArith _ -> ()

let print_wait fmt el =
  List.iter (fun x -> Format.fprintf fmt "%a " Term.print x) el

let print_queue fmt el =
  let rec print_trans q =
    if PersistentQueue.is_empty q then ()
    else
      begin
	let x,r = PersistentQueue.pop q in 
	Format.fprintf fmt "%a " Term.print x;
	print_trans r
      end 
  in print_trans el

let print_interpret_env_file f (env,locks, cond, sem) name app_procs=
  let f = Format.formatter_of_out_channel f in
  Format.fprintf f "\nSTEP\nAfter transition %a(" Hstring.print name;
  Hstring.print_list "," f app_procs;
  Format.fprintf f ")\n";
  Env.iter(fun k {value = v} ->
    Format.fprintf f "%a : " Term.print k; print_val f v; Format.fprintf f "\n"
  ) env;
  Format.fprintf f  "%a" Pretty.print_line ();
  Format.fprintf f "Lock Queues:\n";
  LockQueues.iter (fun k el ->
    Format.fprintf f  "%a : { " Term.print k; print_queue f el; Format.fprintf f "}\n") locks;
  Format.fprintf  f "%a" Pretty.print_line ();
    Format.fprintf f "Condition wait pools:\n";
  Conditions.iter (fun k el ->
    Format.fprintf f "%a : { " Term.print k;  print_wait f el; Format.fprintf f " }\n") cond;
  Format.fprintf  f "%a" Pretty.print_line ();
  Format.fprintf f "Semaphore wait lists:\n";
  Semaphores.iter (fun k el ->
    Format.fprintf f "%a : { " Term.print k; print_wait f el; Format.fprintf f " }\n") sem;
  Format.fprintf  f "%a" Pretty.print_line ();
  Format.fprintf  f "\n"


    
let execute_random3 fmt glob_env trans all_procs unsafe applied_trans orig_env main_bt_env steps tr_table =
  let backtrack_env = ref main_bt_env in
  (*let trace = ref [] in*)
  let steps = ref steps in
  let dfile = Filename.basename Options.file in
  let open_file = open_out (dfile^".txt") in
  print_header open_file dfile;
  Random.self_init ();
  let running_env = ref glob_env in
  let transitions = ref (Array.of_list (all_possible_transitions glob_env trans all_procs false)) in 
  let running = ref true in
  let queue = ref applied_trans in 
  while !running do
    try
      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (apply,apply_procs) = !transitions.(rand) in
      let tr_num = fresh_back () in
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in
      running_env := new_env;
      incr steps;
      transitions := Array.of_list (all_possible_transitions !running_env trans all_procs true);
      let lp = Array.length !transitions in
      Hashtbl.add tr_table tr_num (apply.tr_name, apply_procs);
      queue := PersistentQueue.push (tr_num, apply.tr_name,apply_procs, l, lp) !queue;
      check_unsafe !running_env unsafe;
      print_interpret_env_file open_file !running_env apply.tr_name apply_procs;
      if tr_num mod !step_flag = 0 then
	backtrack_env := Backtrack.add tr_num (apply.tr_name, apply_procs, new_env) !backtrack_env(*;
      trace := running_env :: !trace*)
    with
      | TopError Deadlock ->
	deadlock := true;
	close_out open_file;
	Format.fprintf fmt
	  "@{<b>@{<fg_red>WARNING@}@}: Deadlock reached@."; running := false;
	(*backtrack_replay !running_env ~trace:!trace !queue orig_env !backtrack_env !steps*)	 
      | TopError Unsafe ->
	Format.fprintf fmt
	"@{<b>@{<fg_red>WARNING@}@}: Unsafe state reached. Do you wish to continue? (y/n)@.";
	begin
	  let rec decide () =
	    let inp = read_line () in
	    match inp with
	      | "y" -> ()
	      | "n" -> running := false; close_out open_file
	      | _ -> Format.fprintf fmt "Invalid input@."; decide ()
	  in decide ()
	end 
      | Stdlib.Sys.Break -> close_out open_file; running := false; Format.printf "@."
      | TopError StopExecution ->  close_out open_file; running := false
      | s ->  close_out open_file;
	let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
	assert false
  done;
  close_out open_file;
  !queue, !running_env, !backtrack_env, !steps


let pick_random fmt glob_env trans all_procs unsafe applied_trans orig_env main_bt_env steps tr_table =
  let transitions =
    Array.of_list (all_possible_transitions glob_env trans all_procs false)
  in
  try 
  let l = Array.length transitions in
  if l = 0 then raise (TopError Deadlock);
  let rand = Random.int l in
  let (apply,apply_procs) = transitions.(rand) in
  Format.printf "Picked and applied a random transition from %d possible\n\
                 Transition: %a(%a)@."
    l Hstring.print apply.tr_name Variable.print_vars apply_procs;
  let tr_num = fresh_back () in
  let new_env = apply_transition apply_procs apply.tr_name trans glob_env in
  let steps = steps + 1 in
  let l2 = all_possible_transitions new_env trans all_procs true in
  let lp =
    if l2 = [] then
      begin
	deadlock := true;
	Format.fprintf fmt "@{<b>@{<fg_red>WARNING@}@}: Deadlock reached@.";
	0
      end
    else
      List.length l2
  in 
  Hashtbl.add tr_table tr_num (apply.tr_name, apply_procs);
  let queue = PersistentQueue.push (tr_num, apply.tr_name,apply_procs, l, lp) applied_trans in
  check_unsafe new_env unsafe;
  let new_backtrack = 
    if tr_num mod !step_flag = 0 then
      Backtrack.add tr_num (apply.tr_name, apply_procs, new_env) main_bt_env
    else main_bt_env
  in
  queue, new_env, new_backtrack, steps
  with
    | TopError Deadlock ->
      deadlock := true;
      Format.fprintf fmt "@{<b>@{<fg_red>WARNING@}@}: Deadlock reached@.";
      applied_trans, glob_env, main_bt_env, steps
    | TopError Unsafe ->
	Format.fprintf fmt
	  "@{<b>@{<fg_red>WARNING@}@}: Unsafe state reached@.";
      applied_trans, glob_env, main_bt_env, steps
    | s -> 
      let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
      applied_trans, glob_env, main_bt_env, steps
  

  
  

    
let dump_in_file env file = assert false



let replay_all_steps_pre fmt s1 s2 benv first =
  let count = ref s1 in
  let old = ref first in
  Format.printf "Press enter to continue each time@.";
  while !count <> s2 do
    ignore(read_line ());
    incr count;
    let tr, tr_args, be = Backtrack.find !count benv in 
    Format.printf "After Step %d, transition %a(%a)@." !count Hstring.print tr Variable.print_vars tr_args;
    print_debug_color_env fmt be !old;
    old := be
  done;
  Format.printf "Rerun Terminated@."


let replay_all_steps_not_pre fmt s1 s2 benv htbl transitions first=
  let count = ref s1 in
  let old = ref first in 
  let _,_, en = Backtrack.find s1 benv in 
  let en = ref en in
  Format.printf "Press enter to continue each time@.";
  while !count <> s2 do
    ignore(read_line ());
    incr count;
    let tr, tr_args = Hashtbl.find htbl !count in
    let new_env = apply_transition tr_args tr transitions !en in
    en := new_env;
    Format.printf "After Step %d, transition %a(%a)@." !count Hstring.print tr Variable.print_vars tr_args;
    print_debug_color_env fmt new_env !old;
    old := new_env
  done;
  Format.printf "Rerun Terminated@."    
    
  
      
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


let replay fmt s1 s2 backtrack htbl transitions =
  Format.eprintf "s1 is: %d@." s1;
  Format.eprintf "backtrack: %a@." print_backtrace_env backtrack;
  let tr,tr_args, be = Backtrack.find s1 backtrack in
  ignore (Sys.command "clear");
  Format.printf "Rerunning transitions from Step %d to Step %d " s1 s2; 
  let f = 
    if !step_flag <> 1 then
      begin
	Format.printf "[flag <> 1 : intermediate envs will be recomputed]@.";
	false
      end 
    else
      begin
	Format.printf "[flag = 1 : intermediate envs will not be recomputed]@.";
	true
      end
  in
  Format.printf "Starting from Step %d, post transition %a(%a)@." s1 Hstring.print tr Variable.print_vars tr_args;
  Format.printf "%a@." print_debug_env be;
  if f then replay_all_steps_pre fmt s1 s2 backtrack be
  else replay_all_steps_not_pre fmt s1 s2 backtrack htbl transitions be 

  
let clear_htbl tbl step all =
  let step = step + 1 in
  let all = all + 1 in
  let rec aux count =
    if count = all then ()
    else
      begin
	Hashtbl.remove tbl count;
	aux (count + 1)
      end
  in aux step

let clear_back benv step all =
  let rec aux count env =
    if count= all then env
    else
      begin
	let e =
	  Backtrack.remove count env in 
	aux (count + 1) e
      end
  in aux step benv

let clear_queue queue step  =
  let rec aux count qn qold =
    if count = step then qn
    else
      begin
	let el,rem = PersistentQueue.pop qold in
	let q = PersistentQueue.push el qn in
	aux (count+1) q rem 
      end
  in aux 0 PersistentQueue.empty queue


  
    
    
let setup_env tsys sys =
  Sys.catch_break true;
  let fmt = Format.std_formatter in
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
	     LockQueues.add x (PersistentQueue.empty) acc_lock,
	    cond_acc, sem_acc)
	  else
	    if is_condition ty then
	      Env.add x throwaway acc , LockQueues.add x (PersistentQueue.empty) acc_lock, Conditions.add x [] cond_acc, sem_acc
	    else
	      if is_semaphore ty then
		Env.add x throwaway acc, acc_lock, cond_acc, Semaphores.add x [] sem_acc
	      else 
		(Env.add x throwaway acc , acc_lock, cond_acc, sem_acc)
	| Access(arr,arps) ->
	  let _,ty = Smt.Symbol.type_of arr in
	  if is_lock ty then
	    (Env.add x throwaway acc , LockQueues.add x (PersistentQueue.empty) acc_lock, cond_acc, sem_acc)
	  else
	    if is_condition ty then
	      Env.add x throwaway acc , LockQueues.add x (PersistentQueue.empty) acc_lock, Conditions.add x [] cond_acc, sem_acc
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
  let original_env = env_final, lock_queue, cond_sets, semaphores in 
  let global_env = ref (env_final,lock_queue, cond_sets, semaphores) in
  let applied_trans = ref PersistentQueue.empty in
  let backtrack_env = ref Backtrack.empty in
  let steps = ref 0 in

  let tr_table = Hashtbl.create 10 in

  let s1 = String.make Pretty.vt_width '*' in
  let s2 = String.make ((Pretty.vt_width-7)/2) ' ' in
  let s3 = String.make ((Pretty.vt_width-22)/2) ' ' in

  ignore (Sys.command "clear");

  Format.printf "@{<b>@{<fg_cyan>%s@}@}" s1;
  Format.printf "%sCubicle%s@." s2 s2;
  Format.printf "%sInterpreter & Debugger%s@." s3 s3;
  Format.printf "@{<b>@{<fg_cyan>%s@}@}@." s1;

  print_help fmt;

  (*Format.printf "TODO--some kind of intro message and something about setting flag @.";*)
  
  while !interpret_bool do
    try
      flush stdout; Format.printf "> %!";
      let inp = read_line () in      
      let tts = Parser.toplevel Lexer.token (Lexing.from_string inp) in
      
      (match tts with
	| TopExec -> let ap, g, be, ste =
		       execute_random3 fmt !global_env
			 transitions procs sys.unsafe !applied_trans [] !backtrack_env !steps tr_table
		     in
		     global_env := g;
		     applied_trans := ap;
		     backtrack_env := be;
		     steps := ste
		     (*print_applied_trans fmt ap*)
	| TopTransition tl ->
	  let temp =
	    try
	      List.fold_left (fun acc t ->
		match t with
		  | (n, []) ->
		    let ord = fresh_back () in
		    applied_trans := PersistentQueue.push (ord,n,[],-1,-1) !applied_trans;
		    let pe = apply_transition [] n transitions acc in
		    if ord mod !step_flag = 0 then
		      backtrack_env := Backtrack.add ord (n,[], pe) !backtrack_env;
		    incr steps;
		    Hashtbl.add tr_table ord (n,[]);
		    pe 
		    
		  | (n,l) ->		    
		    check_duplicates l;
		    let ord = fresh_back () in	    
		    applied_trans := PersistentQueue.push (ord,n,l,-1,-1) !applied_trans;
		    let pe = apply_transition l n transitions acc in
		    if ord mod !step_flag = 0 then
		      backtrack_env := Backtrack.add ord (n,l,pe) !backtrack_env;
		    Hashtbl.add tr_table ord (n,l);	       
		    incr steps;
		    
		    pe 
	      ) !global_env tl
	    with
	      | TopError (FalseReq fr) ->
		Format.printf "%a@." top_report (FalseReq fr); !global_env in
	  global_env := temp;	  	  
	| TopShowEnv -> print_interpret_env fmt !global_env 
	| TopHelp -> print_help fmt
	| TopClear -> ignore (Sys.command "clear")

	| TopBacktrack i->
	  if i mod !step_flag <> 0 then raise (TopError (CannotBacktrack i));
	  Format.printf
	    "@{<b>@{<fg_magenta>WARNING@}@}\n\
             Backtracking will clean debug environment:\n\
             all execution traces and saved environments after Step %d will be erasedt@." i;
	  let _,_, e = Backtrack.find i !backtrack_env in
	  global_env := e;
	  clear_htbl tr_table i !steps;
	  backtrack_env := clear_back !backtrack_env i !steps;
	  btracks := (1, i, !steps)::!btracks;
	  applied_trans := clear_queue !applied_trans i;
	  
	    
	| TopFlag f -> step_flag := f; Format.printf  "States will be saved every %d steps@." f 
	| TopShowTrace -> print_debug_trans_path fmt !applied_trans !step_flag
	| TopReplayTrace -> replay fmt 1 !steps !backtrack_env tr_table transitions
	| TopGoto s -> assert false
	  
	| TopRerun(b,e) ->
	  if b mod !step_flag <> 0 then raise (TopError (StepNotMod b));
	  if e > !steps then raise (TopError (StepTooBig (e,e)));
	  replay fmt b e !backtrack_env tr_table transitions
	  
					      
	| TopCurrentTrace -> Hashtbl.iter (fun k (n,pr) ->
	  Format.printf "Step %d: transition %a(%a)@." k Hstring.print n Variable.print_vars pr)
	  tr_table
	  
	| TopWhy(tn,tpl) ->
	  explain tpl tn transitions !global_env
	| TopDebugHelp -> print_debug_help fmt
	| TopDebugOff -> assert false
	    
	| TopPre(tn,tp) -> (*let _t = Trans.find tn transitions in*)
			   give_pre !global_env tsys.t_trans
	  
	| TopAll ->	  	  
	  let l = all_possible_transitions !global_env transitions procs false in
	  if l = [] then
	    begin
	      deadlock := true;
	      raise (TopError Deadlock)
	    end
	  else
	    print_poss_trans fmt l
	| TopUnsafe -> check_unsafe !global_env sys.unsafe 
	| TopRestart ->
	  global_env := original_env;
	  applied_trans := PersistentQueue.empty;
	  backtrack_env := Backtrack.empty;
	  Hashtbl.reset tr_table;
	  print_interpret_env fmt !global_env
	| TopGenProc -> global_env := generate_process !global_env num_procs tsys
	| TopPrintSys -> Ptree.print_system fmt sys

	| TopRandom ->
	  let ap, g, be, ste =
	    pick_random fmt !global_env
	      transitions procs sys.unsafe !applied_trans [] !backtrack_env !steps tr_table
	  in
	  global_env := g;
	  applied_trans := ap;
	  backtrack_env := be;
	  steps := ste
		       
		       
	  
	| TopAssign(name,n, tt) ->
	  (*TO DO FOR CONSTRUCTORS: check that it belongs to type ++ deal with SUBTYPING*)
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
      | TopError e -> Format.printf "%a@." top_report e
      | End_of_file  -> interpret_bool := false
      | Stdlib.Sys.Break -> Format.printf "@."
      | s ->  (*let e = Printexc.to_string s in *)Format.printf "%a@."top_report (InputError)
      
  done 
  
