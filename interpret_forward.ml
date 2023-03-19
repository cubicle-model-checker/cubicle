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

exception OKCands of Node.t list
  

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

let visited_states = ref []
let hCount = Hashtbl.create 100
let system_sigma_en = ref []
let system_sigma_de = ref []

let execute_random_forward glob_env trans all_procs unsafe depth =
  let steps = ref 0 in
  Random.self_init ();
  let running_env = ref glob_env in
  let transitions = ref (Array.of_list (all_possible_transitions glob_env trans all_procs false)) in 
  let queue = ref PersistentQueue.empty in 
  while !steps < depth do


    (*let v_s = env_to_satom !running_env in
    let en_v_s = SAtom.subst !system_sigma_en v_s in*)
    (*let de_v_s = SAtom.subst !system_sigma_de en_v_s in*)

    (*Format.eprintf "Comparing norm and de: %a and %a@." SAtom.print v_s SAtom.print en_v_s;*)
    
    visited_states := (env_to_satom !running_env)::!visited_states;
    try
      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (apply,apply_procs) = !transitions.(rand) in

      

      
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in
      queue := PersistentQueue.push (apply.tr_name, apply_procs) !queue;
      check_unsafe new_env unsafe;
      running_env := new_env;
      incr steps;
      transitions := Array.of_list (all_possible_transitions !running_env trans all_procs true);
      (*count seen states*)
      let hash = hash_full_env new_env in
      begin
      try
	let he,ee = Hashtbl.find hCount hash in
	Hashtbl.replace hCount hash ((he+1),ee)
      with Not_found ->
	Hashtbl.add hCount hash (1,new_env)
      end
      
    with
      | TopError Deadlock ->
	Format.printf 
	  "@{<b>@{<fg_red>WARNING@}@}: Deadlock reached@."; steps := depth
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



let semaphore_init s =
  match s with
    | Const i -> let x = int_of_consts i in VSemaphore x
    | Elem(_, SystemProcs) -> VSemaphore !sys_procs
    | Arith _ -> VArith s
    | _ -> assert false
			

      
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

let run env trans procs unsafe count depth =
  let rec aux count  =
    match count with
      | 0 ->
	let stats = Hashtbl.stats hCount in 
	Format.printf "Forward run complete [%d runs of %d depth for %d procs]\n\
            Visited states: %d\n\
            Unique states:%d@." Options.rounds Options.depth_ib Options.int_brab (Options.depth_ib * Options.rounds) (stats.Hashtbl.num_bindings)
      | _ ->
	execute_random_forward env trans procs unsafe depth;
	aux (count-1)
  in
  aux count



    

let throwaway = Elem(Hstring.make "UNDEF", Glob)


let init tsys = 
  Sys.catch_break true;
  let fmt = Format.std_formatter in
  (*generate X distinc procs*)
  let num_procs = Options.get_interpret_procs () in
  let procs = Variable.give_procs num_procs in

  (*set one sigma for the whole system*)
  let p_m = List.map (fun x -> let p = Hstring.view x in
			       Hstring.make("mapped_"^p)) procs in
  system_sigma_en := Variable.build_subst procs (List.rev procs) ;
  system_sigma_de := Variable.build_subst p_m procs;
  
  (*all terms for the procs, i.e generate instantiated array terms*)
  (* var X[proc]: bool --> X[#1], X[#2] ...  *)
  let var_terms = Forward.all_var_terms procs tsys in
  let const_list = List.map (fun x -> Elem(x, Glob)) tsys.t_consts in
  let var_terms = Term.Set.union var_terms (Term.Set.of_list const_list) in 
  sys_procs := Options.get_interpret_procs ();
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

  run original_env transitions procs unsafe Options.rounds Options.depth_ib 
  

let test_cands cands =
  let rec aux env rem = 
    match env, rem with
      | [], [] -> None
      | hd::tl, [] -> None
      | [], rem -> raise (OKCands rem)
      | hd::tl, _ ->
	let r =
	  List.fold_left (fun acc x ->
	    if SAtom.subset x.cube.litterals hd then acc else x::acc) [] rem
	in aux tl r
  in aux !visited_states cands

let first_good_candidate n =
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
      let cands = 
	List.fold_left (fun acc sigma ->
	  (Node.create ~kind:Approx (Cube.subst sigma s.cube))::acc)[] d
      in
	test_cands cands
    ) None n   
  with
    | OKCands rem ->
      
      let l = List.hd (List.rev rem) in
      Format.eprintf "APPROX: %a -- %d@." Node.print l (List.length rem);
      Some (l)
