open Interpret_calc
open Interpret_types
open Interpret_errors
open Ast
open Types


(*
  val init : Ast.t_system -> unit
    (** Initialize the oracle on a given system *)


    val first_good_candidate : Node.t list -> Node.t option 
    (** Given a list of candidate invariants, returns the first one that seems
        to be indeed an invariant. *)

end


*)

let visited_states = ref []
let visit_count = ref 0
let overall = ref 0
let hCount = Hashtbl.create 100
let system_sigma_en = ref []
let system_sigma_de = ref []
module STMap = Map.Make (Types.Term)


let env_to_satom_map (env,_,_,_) =
  Env.fold (fun key {value = el} acc ->
    (*Format.eprintf "my key: %a@." Term.print key;*)
    match el with
      | VGlob el -> assert false
      | VProc el -> STMap.add key (Elem(el, Var)) acc 
      | VConstr el -> STMap.add key (Elem(el, Constr)) acc
      | VAccess(el,vl) -> assert false
      | VInt i -> let i = ConstInt (Num.num_of_int i) in
		  let m = MConst.add i 1 MConst.empty in
		  STMap.add key (Const(m)) acc
      | VReal r -> let r = ConstReal (Num.num_of_int (int_of_float r)) in
		   let m = MConst.add r 1 MConst.empty in
		   STMap.add key (Const(m)) acc
      | VBool _ -> assert false
      | VArith _ -> assert false
      | _-> acc   
  ) env STMap.empty
    
let env_to_satom (env,_,_,_) =
  Env.fold (fun key {value = el} acc ->
    match el with
      | VGlob el -> SAtom.add (Comp(key, Eq, Elem(el, Glob))) acc 
      | VProc el -> SAtom.add (Comp(key, Eq, Elem(el, Var))) acc
      | VConstr el -> SAtom.add (Comp(key, Eq, Elem(el, Constr))) acc
      | VAccess(el,vl) -> SAtom.add (Comp(key, Eq, Access(el, vl))) acc
      | VInt i -> let i = ConstInt (Num.num_of_int i) in
		  let m = MConst.add i 1 MConst.empty in
		   SAtom.add (Comp(key, Eq, Const(m))) acc
      | VReal r -> let r = ConstReal (Num.num_of_int (int_of_float r)) in
		   let m = MConst.add r 1 MConst.empty in
		   SAtom.add (Comp(key, Eq, Const(m))) acc
      | VBool _ -> assert false
      | VArith _ -> assert false
      | _-> acc   
  ) env SAtom.empty



let env_to_map env =
  SAtom.fold (fun atom acc ->
    match atom with
      | Comp(Elem(_, Glob), op, Elem(_, Glob)) 
      | Comp(Elem(_, Glob), op, Access _)
      | Comp(Access _, op, Elem(_, Glob))
      | Comp (Access _, op, Access _)
	-> assert false
      | Comp(((Elem(_, Glob)) as t1), Eq, t2) 
      | Comp(((Access _ ) as t1), Eq, t2)
      | Comp(t2, Eq, ((Elem(_, Glob)) as t1))
      | Comp (t2, Eq, ((Access _) as t1))
	-> STMap.add t1 t2 acc
      | _ -> assert false
  ) env STMap.empty
    

exception OKCands of Node.t list


let markov_entropy_detailed glob tsys all_procs trans steps det_flag=
  Random.self_init ();
  let taken = ref 0 in
  let transitions = ref (Array.of_list (all_possible_transitions glob trans all_procs false))
  in 
  let running_env = ref glob in
  let accept = ref 0  in
  let reject = ref 0 in
  let w1 = ref (entropy_env glob trans all_procs) in 
  while  !taken < steps do
    try
      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (proposal,prop_procs) = !transitions.(rand) in
      
      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in
      let w2 = entropy_env temp_env trans all_procs in
      let flag =
	if w2 > !w1 then
	  begin
	    true
	  end
	else
	  begin
	    let prob = 2.718281828**(w2 -. !w1) in
	    let rand_prob = Random.float 1.0 in
	    if prob > rand_prob then true else false 
	end
      in
      if flag then
	begin
	  incr overall;
	  incr taken;
	  let hash = hash_full_env temp_env in
	  begin
	    try
	      let he,ee = Hashtbl.find hCount hash in
	      Hashtbl.replace hCount hash ((he+1),ee)
	    with Not_found ->
	      Hashtbl.add hCount hash (1,temp_env);
	      let ee = env_to_satom_map temp_env in
	      visited_states := ee::!visited_states;
	      incr visit_count;
	  end;
	  
	  transitions := Array.of_list (all_possible_transitions temp_env trans all_procs true);
	  incr accept;
	  w1 := w2;
	  running_env := temp_env;	  
	end
      else
	begin
	  incr reject
	end(*;
      incr taken*)
    with
      | TopError Deadlock -> taken := steps
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> taken := steps
  done;
  if Options.int_brab_quiet then 
  Format.eprintf "Accepted: %d, Rejected: %d@." !accept !reject
  





    


let markov_entropy_detailed2 glob tsys all_procs trans steps det_flag=
  Random.self_init ();
  (*let proc_count = Array.make (Options.get_interpret_procs ()) 0 in*)
  let proc_count = Array.make Options.int_brab 0 in  
  let t_count = Hashtbl.create 10 in 
  let matrix =
    if det_flag then
      create_detailed_hash tsys all_procs
    else
      create_transition_hash tsys
  in
  let trt =
    List.fold_left (fun acc el->
      let args = el.tr_args in
      let num_args = List.length args in
      let tr_procs = all_arrange num_args all_procs in
      if tr_procs = [] then
	  (el,[])::acc
      else
	begin
	  List.fold_left (fun acc_t procs ->
	    (el, procs)::acc_t      
	  ) acc tr_procs
	
	end 
    ) [] tsys
  in
  let els = List.length trt in 
  let tr_array = Array.of_list trt in

  let taken = ref 0 in
  let before = Hstring.make "Init" in
  let before = ref before in
  let transitions = ref (Array.of_list (all_possible_transitions glob trans all_procs false)) in 
  let running_env = ref glob in
  let accept = ref 0  in
  let reject = ref 0 in
  let w1 = ref (entropy_env glob trans all_procs) in 
  while  !taken < steps do
    try

      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (proposal,prop_procs) = !transitions.(rand) in
      
      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in
      
      let w2 = entropy_env temp_env trans all_procs in
      let flag =
	if w2 > !w1 then
	  begin
	    true
	  end
	else
	  begin
	    let prob = 2.718281828**(w2 -. !w1) in
	    let rand_prob = Random.float 1.0 in
	    if prob > rand_prob then true else false 
	end
      in
      let prop_hs =
	if det_flag then
	  trans_proc_to_hstring proposal.tr_name prop_procs
	else
	  proposal.tr_name 
      in 
      if flag then
	begin
	(*let ee = env_to_satom temp_env in
	  let ee = env_to_map ee in *)
	  let ee = env_to_satom_map temp_env in
	  visited_states := ee::!visited_states;
	  (*visited_states := (env_to_satom temp_env)::!visited_states;*)
	  transitions := Array.of_list (all_possible_transitions temp_env trans all_procs true);
	  incr accept;
	  w1 := w2;
	  running_env := temp_env;
	  let pair = (!before, prop_hs) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found ->
	      Hashtbl.add matrix pair 1
	  end;
	  before := prop_hs;
	  
	  let hash = hash_full_env temp_env in
	  begin
	    try
	      let he,ee = Hashtbl.find hCount hash in
	      Hashtbl.replace hCount hash ((he+1),ee)
	    with Not_found ->
	      Hashtbl.add hCount hash (1,temp_env)
	  end;
	  let appl = procs_to_int_list prop_procs in
	  List.iter (fun x ->
	    proc_count.(x-1) <- proc_count.(x-1) + 1) appl;
	  begin
	    try
	      let htc= Hashtbl.find t_count prop_hs in
	      Hashtbl.replace t_count prop_hs (htc+1)
	    with Not_found -> Hashtbl.add t_count prop_hs 1
	  end ;
	end
      else
	begin
	  incr reject
	end;
      incr taken
    with
      | TopError Deadlock -> taken := steps
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> taken := steps
  done;
  if Options.int_brab_quiet then 
  Format.eprintf "Accepted: %d, Rejected: %d@." !accept !reject
  (*let smost,smtime,overall =
    Hashtbl.fold (fun k (el,envoo) (ak, ael,overall) ->
      if el > ael then (k,el,overall+el) else (ak,ael,overall+el)) !hCount (0,0,0) in
  
  Format.printf "Total entries: %d\n\
                 Total visited: %d\n\
                 State seen most often: %d [%d time(s)] @."
    (Hashtbl.stats !hCount).num_bindings overall smost smtime;*)
  
  (*Array.iteri (fun i a -> Format.eprintf "Proc %d : %d times@." (i+1) a) proc_count;
	  
  Hashtbl.iter (fun k el -> Format.eprintf "Transition %a : %d times@." Hstring.print k el) t_count;
  let num = Hashtbl.fold (fun k el acc -> el+acc) t_count 0 in
  Format.eprintf "Total transitions taken: %d@." num;
  (*let num = float (num-1)  in *)
  Hashtbl.iter (fun (k,k1) el -> Format.eprintf "%a->%a : %d @." Hstring.print k Hstring.print k1 el ) matrix*)

  








    

let rec extract_proc_from_term term acc =
  match term with
    | Access(_, l) -> List.fold_left (fun acc2 el -> el::acc2) acc l
    | Elem(p, Var) -> p::acc
    | Arith (t,_) -> extract_proc_from_term t acc 
    | _ -> acc
    
      
let gen_mapping pl =
  let ml, _ =
    List.fold_left (fun (acc,count) x ->
      let v = Hstring.make("mapped_"^(string_of_int count))
      in
      (v::acc, count+1)
    ) ([],0) pl in
  let ml = List.rev ml in
  Variable.build_subst pl ml

  

let extract_procs sa =
  let procs =
    SAtom.fold (fun atom acc ->
    match atom with
      | Comp(t1, _, t2) ->
	let p1 = extract_proc_from_term t1 acc in
	extract_proc_from_term t2 p1
      | Ite _ -> assert false
      | True | False -> acc	
    ) sa []
  in
  let sorted = List.sort_uniq Hstring.compare procs in
  (*List.iter (fun x -> Format.eprintf "%a@." Hstring.print x) sorted;*)
  sorted
    

let print_forward_trace fmt el =
  let rec print_trans q =
    if PersistentQueue.is_empty q then ()
    else
      begin
	let (x,p),r = PersistentQueue.pop q in 
	Format.printf "%a(%a)@." Hstring.print x Variable.print_vars p;
	print_trans r
      end 
  in print_trans el
  



let execute_random_forward glob_env trans all_procs unsafe depth =
  let steps = ref 0 in
  Random.self_init ();
  let running_env = ref glob_env in
  let transitions = ref (Array.of_list (all_possible_transitions glob_env trans all_procs false)) in 
  let queue = ref PersistentQueue.empty in 
  while !steps < depth do
    incr overall;
    let hash = hash_full_env !running_env in
    begin
      try
	let he,ee = Hashtbl.find hCount hash in
	Hashtbl.replace hCount hash ((he+1),ee)
      with Not_found ->
	begin
	  Hashtbl.add hCount hash (1,!running_env);
	  let ee = env_to_satom_map !running_env in
	  visited_states := ee::!visited_states;
	  incr visit_count;
	end
    end;
    
    (*visited_states := (de_v_s)::!visited_states;*)
    
    try

      (*let ggg = Hstring.make "t4_incr_for1" in
      Format.eprintf "Choices:@.";
      Array.iter (fun (x,y) ->
	if Hstring.equal x.tr_name ggg then Format.eprintf "YOYOYOY@." else ();
	Format.eprintf "%a(%a) | " Hstring.print x.tr_name Variable.print_vars y) !transitions;
      Format.eprintf "@.Chosen:@.";*)

      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (apply,apply_procs) = !transitions.(rand) in
      (*Format.eprintf "%a(%a) : %d\n--------------@." Hstring.print apply.tr_name Variable.print_vars apply_procs rand; *)
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in
      queue := PersistentQueue.push (apply.tr_name, apply_procs) !queue;
      check_unsafe new_env unsafe;
      running_env := new_env;
      incr steps;
      transitions := Array.of_list (all_possible_transitions !running_env trans all_procs true);
      (*count seen states*)
      
    with
      | TopError Deadlock ->
	if Options.int_brab_quiet then
	  begin
	    Format.printf 
	      "@{<b>@{<fg_red>WARNING@}@}: Deadlock reached in %d steps@." !steps;
	    Format.eprintf "%a@." print_forward_trace !queue;
	    Format.eprintf "----@.";
	  end ;
	



	steps := depth
      | TopError Unsafe -> steps := depth;
      	Format.printf 
	"@{<b>@{<fg_red>WARNING@}@}: Unsafe state reached. Stopping exploration.";

      | Stdlib.Sys.Break ->  steps := depth
      | TopError StopExecution ->
	steps := depth
      | s -> 
	let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
	steps := depth
  done
  (*Format.eprintf "%a@." print_forward_trace !queue*)



let semaphore_init s =
  match s with
    | Const i -> let x = int_of_consts i in VSemaphore x
    | Elem(_, SystemProcs) -> VSemaphore !sys_procs
    | Arith _ -> VArith s
    | _ -> assert false
			

      
let init_vals env init =
  if Options.debug_interpreter then Format.eprintf "Init_vals:@.";
  (*let procs = Variable.give_procs (Options.get_interpret_procs ()) in*)
  let procs = Variable.give_procs Options.int_brab in
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
	| Comp (t1, Neq, t2) ->
	  begin
	    match t1, t2 with
	      | Elem(_, Glob), Elem(_, Var) ->
		let temp =
		  Hstring.make ("#" ^ string_of_int(Options.int_brab + 1))
		in
		Env.add t1 (Elem(temp, Var)) sacc
	      | Elem (_, Var), Elem(_,Glob) ->
		let temp =
		  Hstring.make ("#" ^ string_of_int(Options.int_brab + 1))
		in
		Env.add t2 (Elem(temp, Var)) sacc
	      | _ -> assert false
		
	  end
	  
	| Comp (t1, Lt, t2) -> assert false
	| Comp (t1, Le, t2) -> assert false
	| True -> assert false
	| False -> assert false
	| Ite _ -> assert false
	  
    ) el acc
  ) env dnf

let run env trans procs unsafe count depth =
  Random.self_init ();
  let depths = ref [] in 
  let rec aux count  =
    match count with
      | 0 ->
	let stats = Hashtbl.stats hCount in 
	Format.printf "Forward run complete [%d runs of max %d depth for %d procs]\n\
            Visited nodes total: %d\n\
            Visited nodes retained: %d\n\
            Unique states:%d@."
	  Options.rounds
	  Options.depth_ib
	  Options.int_brab
	  !overall
	  !visit_count
	  (stats.Hashtbl.num_bindings);
	if Options.int_brab_quiet then
	  begin
	    Format.printf "Various depths:@.";
	    List.iter (fun x -> Format.printf " %d" x) !depths;
	    Format.printf "@."
	  end 
      | _ ->
	let rand = (Random.int depth) + 1 in
	depths := rand :: !depths;
	execute_random_forward env trans procs unsafe rand;
	aux (count-1)
  in
  aux count


let run_markov env tsys trans procs unsafe count depth =
  Random.self_init ();
  let depths = ref [] in 
  let rec aux count  =
    match count with
      | 0 ->
	let stats = Hashtbl.stats hCount in 
	Format.printf "Forward run complete [%d runs of max %d depth for %d procs]\n\
            Visited nodes total: %d\n\
            Visited nodes retained: %d\n\
            Unique states:%d@."
	  Options.rounds
	  Options.depth_ib
	  Options.int_brab
	  !overall
	  !visit_count
	  (stats.Hashtbl.num_bindings);
	if Options.int_brab_quiet then
	  begin
	    Format.printf "Various depths:@.";
	    List.iter (fun x -> Format.printf " %d" x) !depths;
	    Format.printf "@."
	  end 
      | _ ->
	let rand = (Random.int depth) + 1 in
	depths := rand :: !depths;
	markov_entropy_detailed env tsys procs trans rand false;
	aux (count-1)
  in
  aux count    



    

let throwaway = Elem(Hstring.make "UNDEF", Glob)


let init tsys = 
  Sys.catch_break true;
  let fmt = Format.std_formatter in
  (*generate X distinc procs*)
  let num_procs = Options.int_brab in
  let procs = Variable.give_procs num_procs in

  (*set one sigma for the whole system*)
  let p_m,_ = List.fold_left (fun (acc, count) x ->
	    let pl = Hstring.make("mapped_"^(string_of_int count))
	    in
	    ((pl,x)::acc, count+1)
  ) ([], 0) procs in
  system_sigma_en := p_m ;
  
  (*system_sigma_de := Variable.build_subst p_m procs;*)
  
  (*all terms for the procs, i.e generate instantiated array terms*)
  (* var X[proc]: bool --> X[#1], X[#2] ...  *)
  let var_terms = Forward.all_var_terms procs tsys in
  let const_list = List.map (fun x -> Elem(x, Glob)) tsys.t_consts in
  let var_terms = Term.Set.union var_terms (Term.Set.of_list const_list) in 
  sys_procs := Options.int_brab;
  (*let all_unsafes = init_unsafe procs sys.unsafe in*)
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
      Env.fold (fun k x acc ->
	match x.value with
	  | VGlob n ->
	    let vg = Env.find (Elem(n,Glob)) acc in
	    begin
	      match vg.value with
		| VGlob n1 ->
		  begin
		    let vg2 = Env.find (Elem (n1,Glob)) acc in
		    let tt = 
		      match vg2.value with
			| VGlob n2 ->
			  {value = random_value vg2.typ; typ = vg2.typ }
			| tt -> vg2
		    in
		    let e1 =  Env.add (Elem(n,Glob)) tt acc in
		    let e2 = Env.add (Elem(n1,Glob)) tt e1 in 
		    Env.add k tt e2 
		  end
		| tt -> Env.add k vg acc 
	    end
	  | _ -> Env.add k x acc
      ) env_final env_final in 
  let env_final =
    Env.mapi (fun k x ->
      (*let ty = Smt.Symbol.type_of k in *)
      match x.value with
	| VArith ta -> let v = eval_arith ta env_final x.typ in
		       {value =  v; typ = x.typ}
	| _ ->
	  x


    ) env_final in
  
  let env_final =
    List.fold_left (fun acc x ->
      Env.add (Elem(x, Var)) {value = VAlive; typ = ty_proc} acc
  ) env_final procs
  in

  let t_transitions = List.map (fun x -> x.tr_info) tsys.t_trans in 
  let transitions =
    List.fold_left ( fun acc t ->    
      Trans.add t.tr_name t acc ) Trans.empty t_transitions in
  let original_env = env_final, lock_queue, cond_sets, semaphores in 
  (*let global_env = ref (env_final,lock_queue, cond_sets, semaphores) in
  let applied_trans = ref PersistentQueue.empty in
  let backtrack_env = ref Backtrack.empty in
  let steps = ref 0 in*)
  let unsafe = List.map (fun x -> 0,x.cube.vars ,x.cube.litterals) tsys.t_unsafe in
  let unsafe = init_unsafe procs unsafe in

  if Options.mrkv_brab = 1 then
    run_markov original_env t_transitions transitions procs unsafe Options.rounds Options.depth_ib
  else 
  run original_env transitions procs unsafe Options.rounds Options.depth_ib
  
  

(*let test_cand2s cands =
  let rec aux env rem = 
    match env, rem with
      | [], [] -> None
      | hd::tl, [] -> None
      | [], rem -> raise (OKCands rem)
      | hd::tl, _ ->
	let r =
	  List.fold_left (fun acc x ->
	    (*let pl1 = extract_procs x.cube.litterals in
	    let map1 = gen_mapping pl1 in
	    let enc_1 = SAtom.subst map1 x.cube.litterals in

	    let pl2 = extract_procs hd in
	    let map2 = gen_mapping pl2 in
	    let enc_2 = SAtom.subst map2 hd  in

	    let de1 = SAtom.subst !system_sigma_en enc_1 in
	    let de2 = SAtom.subst !system_sigma_en enc_2 in *)
	    
	    (*let x = SAtom.subst !system_sigma_en x.cube.litterals in
	    let hd = SAtom.subst !system_sigma_en hd in*) 
	  if SAtom.subset x.cube.litterals hd then acc else x::acc

	    (*if SAtom.subset de1 de2 then acc else x::acc*)



	  ) [] rem
	in aux tl r
  in aux !visited_states cands*)


let temp =
  let hs = Hstring.make "ShWbMsg_Cmd" in
  Elem(hs, Glob)


let test_vals op v1 v2 =
  match op with
    | Eq -> Term.compare v1 v2 = 0    
    | Neq -> Term.compare v1 v2 <> 0 
    | Lt -> Term.compare v1 v2 = -1 
    | Le -> Term.compare v1 v2 = -1 || Term.compare v1 v2 = 0



let test_cands cands =
  (*List.iter (fun x -> Format.eprintf "ENV:%a \\ @." SAtom.print x) !visited_states;*)
  let rec aux env r =
    match env, r with
      | [], f -> if f then raise (OKCands cands) else None
      | env_map::tl,_ ->
	begin
	  let flag =
	    List.fold_left (fun acc node ->
	      let nlitts = node.cube.litterals in
	      
	      let f =
		SAtom.fold (fun atom flagL ->
		  let f = 
		    match atom with
		      | Comp(t1, op, t2) ->
			begin
			  match t1, t2 with
			    | Elem(_, Glob), Elem(_, Glob)
			    | Elem(_, Glob), Access _
			    | Access _, Elem (_, Glob)
			    | Access _, Access _ 
			      ->
			      
			      let v1 = STMap.find t1 env_map in
			      let v2 = STMap.find t2 env_map in
			      (*Format.eprintf "t1 %a v1 is %a\nt2 %av2 is %a@." Term.print t1 Term.print t2 Term.print v1 Term.print v2;*)
			      test_vals op v1 v2
			    | Elem (_, Glob), _ ->

			      let v1 = STMap.find t1 env_map in
			      test_vals op v1 t2
			    | _, Elem(_, Glob) ->

			      let v1 = STMap.find t2 env_map in 
			      test_vals op t1 v1
			    | Access _, _ ->
			      (*Format.eprintf "t1: %a, t2: %a@." Term.print t1 Term.print t2;
			      Format.eprintf "Env:@.";
			      STMap.iter (fun key el -> Format.eprintf "key %a === %a@." Term.print key Term.print el) env_map;*)
			      let v1 = STMap.find t1 env_map in
			      test_vals op v1 t2
			    | _,  Access _ ->
			      let v1 = STMap.find t2 env_map in 
			      test_vals op t1 v1
			    | _ -> assert false    
			end
		      | Ite _ -> assert false
		      | True -> true
		      | False -> false (*??*)
		  in
		  f::flagL
		) nlitts []
	      in
	      (List.for_all (fun x -> x) f)::acc
	    ) [] cands
	  in

	  
	  let rec temp l ff=
	    match l with
		| [] -> ff
		| hd::tl ->
			   if hd then temp tl (false&&ff) else temp tl ff
			   
	  in
	  let flag = temp flag true in 
	  if flag then
	    aux tl true
	  else
	    begin
	      (*Format.eprintf "candidates denied:@.";
	      List.iter (fun x -> Format.eprintf "%a//@." Node.print x) cands;*)
	      None
	    end
	end

  in aux !visited_states true



(*let test_cands cands =
  let rec aux env r = 
    match env,r with
      | [], f -> if f then raise (OKCands cands) else None
      | hd::tl, _ ->
	let e = Cubetrie.empty in
	let n = Node.create (Cube.create_normal hd) in 
	let e = Cubetrie.add_node n e in
	let g = List.fold_left (fun acc node ->
	  let temp = Cubetrie.delete_subsumed node e in
	  if Cubetrie.is_empty temp then false&&acc else acc) true cands in
	if g then aux tl true
	else None 
	
  in aux !visited_states true*)
  
  
(*
let test_cand2s cands =
  let rec aux env r = 
    match env,r with
      | [], f -> if f then raise (OKCands cands) else None
      | hd::tl, _ ->
	let r =
	  List.fold_left (fun acc x ->
	  if SAtom.subset x.cube.litterals hd then (false&&acc) else acc
	  )true cands
	in
	if r then
	  aux tl true
	else None
  in aux !visited_states true*)

let first_good_candidate3 n =
  (*Format.eprintf "also look at the cool stuff:@.";
  Format.eprintf "Length %d@." (List.length !visited_states);*)
  let num_procs = Options.int_brab in
  let procs = Variable.give_procs num_procs in
  (*Format.eprintf "hello you are now in foraward interpret, look at the nodes!@.";*)
  (*List.iter (fun x -> Format.eprintf "%a\n------@." Node.print x) n;*)
  (*Format.eprintf "also look at the cool stuff: %d@." (List.length !visited_states);*)
  try
    List.fold_left (fun acc s ->
      let d = (Variable.all_permutations (Node.variables s) procs)
      in
      let cands = (*[Node.create ~kind:Approx  s.cube ]*)
	List.fold_left (fun acc sigma ->
	    
	    (Node.create ~kind:Approx (Cube.subst sigma s.cube))::acc)[] d
      in
	test_cands cands
    ) None n   
  with
    | OKCands rem ->  
      let l = List.hd (List.rev rem) in
      (*Format.eprintf "APPROX: %a -- %d@." Node.print l (List.length rem);*)
      Some (l)


let first_good_candidate n =
  
  let num_procs = Options.int_brab in
  let procs = Variable.give_procs num_procs in
  try
    List.fold_left (fun acc s ->
      let d = List.rev (Variable.all_permutations (Node.variables s) procs)
      in
      let cands = 
	List.fold_left (fun acc sigma ->
	  (Node.create ~kind:Approx (Cube.subst sigma s.cube))::acc)[] d
      in
      (*List.iter (fun x -> Format.eprintf "Candidate: %a@." Node.print x) cands;*)
	test_cands cands
    ) None n   
  with
    | OKCands rem ->  
      let l = List.hd ((*List.rev*) rem) in
      (*Format.eprintf "APPROX: %a -- %d@." Node.print l (List.length rem);*)
      Some (l)
