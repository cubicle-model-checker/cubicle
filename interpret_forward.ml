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
let hSCount = Hashtbl.create 100

let system_sigma_en = ref []
let system_sigma_de = ref []
let tr_count = Hashtbl.create 100
let deadlocks = ref (0, [])
module STMap = Map.Make (Types.Term)

type data = {
  state : Interpret_types.global;
  seen : int;
  exit_number : int;
  exit_transitions : (Hstring.t * Variable.t list) list;
  taken_transitions : (Hstring.t * Variable.t list) list;
}

type deadlock_state = {
  dead_state : Interpret_types.global;
  dead_predecessor : Interpret_types.global;
  dead_path : (Hstring.t * Variable.t list) PersistentQueue.t;
  dead_steps : int
}

  
    


    
    
let initial_data = Hashtbl.create 200 (*hash -> data*)
(*env map of initial states to give to Cubicle without having to remap everything*)
let initial_runs = ref []
(*Count how many times each hash seen -- could be mixed with initial data*)  
let initial_count =  Hashtbl.create 100
(*counter for initially visited states so no need to count again*)
let initial_visited = ref 0
(*how many times each transition was seen*)  
let initial_tr_count = Hashtbl.create 100
(*states that deadlocked and how it got there*)
let deadlock_states = Hashtbl.create 10
(*states that led to a deadlock*)
let dead_preds = Hashtbl.create 10

  
let print_forward_trace fmt el =
  let rec print_trans q =
    if PersistentQueue.is_empty q then ()
    else
      begin
	let (x,p),r = PersistentQueue.pop q in
	if PersistentQueue.is_empty r then
	  begin
	    Format.printf "%a(%a) @." Hstring.print x Variable.print_vars p;
	    print_trans r
	  end
	else
	  begin
	    Format.printf "%a(%a) -> " Hstring.print x Variable.print_vars p;
	print_trans r
	  end 
      end 
  in print_trans el
  



let env_to_satom_map (env,_,_,_) =
  Env.fold (fun key {value = el} acc ->
    (*Format.eprintf "my key: %a@." Term.print key;*)
    match el with
      | VGlob el -> (*assert false*) STMap.add key (Elem(el, Glob)) acc
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

let rec choose_first_current_proc proc transitions =
  match transitions with
    | [] -> None
    | (tr,hd)::tl -> if List.exists (fun x -> Hstring.equal x proc) hd then
	Some (tr,hd)
      else choose_first_current_proc proc tl

let choose_current_proc_list proc transitions =
  List.fold_left (fun acc (x,pr)->
    if List.exists (fun x -> Hstring.equal x proc) pr then
      (x,pr)::acc else acc) [] transitions

let rec choose_first_other_proc proc transitions =
  match transitions with
    | [] -> None
    | (tr,hd)::tl -> if List.exists (fun x -> Hstring.compare x proc <> 0) hd then
	Some (tr,hd)
      else choose_first_other_proc proc tl

let choose_other_proc_list proc transitions =
  List.fold_left (fun acc (x,pr)->
    if List.exists (fun x -> Hstring.compare x proc <> 0) pr then
      (x,pr)::acc else acc) [] transitions	


let compare_exits (tr1,p1) (tr2,p2) =
  (Hstring.equal tr1 tr2) && (Variable.compare_list p1 p2 = 0)

let choose_random_of_equals l len=
  (*Random.self_init();*)
  let i = Random.int len in
  (Array.of_list l).(i)

    
let force_procs_forward glob_env trans all_procs  depth p_proc  =
  let steps = ref 0 in
  let running_env = ref glob_env in
  let transitions = ref  (all_possible_transitions glob_env trans all_procs false) in 
  let queue = ref PersistentQueue.empty in
  let old_env = ref glob_env in
  let old_hash = ref (hash_full_env glob_env) in 
  while !steps < depth do
    incr overall;
    try
      let tr_with_proc = choose_current_proc_list p_proc !transitions in
      let choose_from =
	if tr_with_proc = []
	then 
	  Array.of_list (!transitions)
	else Array.of_list (tr_with_proc) in     
      let l = Array.length choose_from in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (apply,apply_procs) = choose_from.(rand) in
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in

      if !steps > 0 then
	begin
	  try
	    let data = Hashtbl.find initial_data !old_hash in
	    Hashtbl.replace initial_data !old_hash
	      { state = data.state;
		seen = data.seen + 1;
		exit_number = data.exit_number;
		exit_transitions = List.filter (fun x ->
		  not (compare_exits x (apply.tr_name, apply_procs))
		) data.exit_transitions;
		taken_transitions = (apply.tr_name, apply_procs)::data.taken_transitions;
	      }
	  with Not_found -> assert false
	end ;
      let hash = hash_full_env new_env in    
      let exits = all_possible_transitions new_env trans all_procs true in

      begin
	try
	  let he, ee = Hashtbl.find initial_count hash in
	  Hashtbl.replace initial_count hash ((he+1),ee)
	with Not_found ->
	  Hashtbl.add initial_count hash (1,new_env);
	  let ee = env_to_satom_map new_env in
	  initial_runs := ee::!initial_runs;
	  incr initial_visited;
	  Hashtbl.add initial_data hash
	    { state = new_env;
	      seen = 0 ;
	      exit_number = List.length exits;
	      exit_transitions = List.map (fun (x,y) -> (x.tr_name, y)) exits;
	      taken_transitions = [];
	    } 
      end;
      begin
	try 
	  let ht_count = Hashtbl.find initial_tr_count apply.tr_name in
	  Hashtbl.replace initial_tr_count apply.tr_name (ht_count+1)
	    with Not_found ->  Hashtbl.add initial_tr_count apply.tr_name 1
      end;
      queue := PersistentQueue.push (apply.tr_name, apply_procs) !queue;
      (*check_unsafe new_env unsafe;*)
      old_hash := hash;
      old_env := !running_env;
      running_env := new_env;
      incr steps;
      transitions := all_possible_transitions !running_env trans all_procs true;
      (*count seen states*)
      
    with
      | TopError Deadlock ->
	let dead_hash = hash_full_env !running_env in
	Hashtbl.add deadlock_states dead_hash { dead_state = !running_env;
						dead_path = !queue;
						dead_steps = !steps;
						dead_predecessor = !old_env} ;
	Hashtbl.add dead_preds !old_hash dead_hash ;
	steps := depth
      | TopError Unsafe -> steps := depth;
      	Format.printf 
	"@{<b>@{<fg_red>WARNING@}@}: Unsafe state reached. Stopping exploration."
      | Stdlib.Sys.Break ->  steps := depth
      | TopError StopExecution ->
	steps := depth
      | s -> 
	let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
	steps := depth
  done
  (*Format.eprintf "For proc: %a@." Hstring.print p_proc;
  Format.eprintf "%a@." print_forward_trace !queue;
  Format.eprintf "-------------------------@."*)




    

let markov_init_run glob tsys all_procs trans steps matrix possibility_matrix =
  (*Random.self_init ();*)
  (*Create the transition matrix to filter out transitions that lead to holes *)
  let before = Hstring.make "Init" in
  let before = ref before in
  
  let taken = ref 0 in
  let transitions = ref (Array.of_list (all_possible_transitions glob trans all_procs false))
  in 
  let running_env = ref glob in
  let queue = ref PersistentQueue.empty in

  let old_env = ref glob in
  let accept = ref 0  in
  let reject = ref 0 in
  let old_hash = ref (hash_full_env glob) in
  let w1 = ref (entropy_env glob trans all_procs) in 

  while  !taken < steps do
    try
      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
(*
      let max_entropy, propList, prop_count =
	Array.fold_left (fun (acc_e, prl,els) (el_t,el_p) ->
	let res = apply_transition el_p el_t.tr_name trans !running_env in
	let w2 = entropy_env res trans all_procs in
	if w2 > acc_e then (w2, [(el_t, el_p)], 1)
	else if w2 = acc_e then (acc_e, (el_t,el_p)::prl, els+1)
	else acc_e,prl, els) (0., [], 0) !transitions
      in

  let proposal,prop_procs = choose_random_of_equals propList prop_count in*)

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
      
	  if !taken > 0 then 
	    begin
	      try 
		let data = Hashtbl.find initial_data !old_hash  in
		
		Hashtbl.replace initial_data !old_hash
		  { state = data.state; 
		    seen = data.seen + 1;
		    exit_number = data.exit_number;
		    exit_transitions =
		      List.filter (fun x ->
			not (compare_exits x (proposal.tr_name, prop_procs))
		      ) data.exit_transitions;
		    taken_transitions = (proposal.tr_name, prop_procs)::data.taken_transitions
		  }
	      with Not_found -> assert false
	    (*shouldn't be raised since you're looking for a state you just added*)
	    end;
	  incr overall;
	  incr taken;
	  let hash = hash_full_env temp_env in
	  let exits = all_possible_transitions temp_env trans all_procs true in
	  begin
	    try
	      let he,ee = Hashtbl.find initial_count hash in
	      Hashtbl.replace initial_count hash ((he+1),ee)
	    with Not_found ->
	      Hashtbl.add initial_count hash (1,temp_env);
	      let ee = env_to_satom_map temp_env in
	      initial_runs := ee::!initial_runs;
	      incr initial_visited;
	      Hashtbl.add initial_data hash
		{ state = temp_env;
		  seen = 0 ;
		  exit_number = List.length exits;
		  exit_transitions = List.map (fun (x,y) -> (x.tr_name, y)) exits;
		  taken_transitions = [];
		} 
	  end;
	  begin
	    try 
	      let ht_count = Hashtbl.find initial_tr_count proposal.tr_name in
	      Hashtbl.replace initial_tr_count proposal.tr_name (ht_count+1)
	    with Not_found ->  Hashtbl.add initial_tr_count proposal.tr_name 1
	  end;

	  let pair = (!before, proposal.tr_name) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found -> Hashtbl.add matrix pair 1
	  end ;
	  before := proposal.tr_name;

	  begin
	    Array.iter (fun (tr,_) ->
	      let paired = (!before, tr.tr_name) in
	      try
		let v = Hashtbl.find  possibility_matrix paired in
		Hashtbl.replace possibility_matrix paired (v+1)
	      with Not_found -> Hashtbl.add possibility_matrix paired 1)
	   !transitions
	  end ;


	  
	  transitions := Array.of_list exits;
	  incr accept;
	  w1 := w2;
	  old_hash := hash;
	  old_env := !running_env;
	  running_env := temp_env;
	  queue := PersistentQueue.push (proposal.tr_name, prop_procs) !queue;
	end
      else
	incr reject	   
	  
    with
      | TopError Deadlock ->
        let dead_hash = hash_full_env !running_env in
	Hashtbl.add deadlock_states dead_hash { dead_state = !running_env;
						dead_path = !queue;
						dead_steps = !taken;
						dead_predecessor = !old_env} ;
		Hashtbl.add dead_preds !old_hash dead_hash ;
	taken := steps
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> taken := steps
  done;
  if Options.int_brab_quiet then 
    Format.eprintf "Accepted: %d, Rejected: %d@." !accept !reject    


let markov_entropy_detailed glob tsys all_procs trans steps curr_round=
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

	  begin
	    try 
	      let (ht_count, seen) = Hashtbl.find tr_count proposal.tr_name in
	      let seen = if seen = -1 then curr_round else seen in  
	      Hashtbl.replace tr_count proposal.tr_name (ht_count+1, seen)
	    with Not_found ->  Hashtbl.add tr_count proposal.tr_name (1, curr_round)
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
      | TopError Deadlock ->
        let d,dl =  !deadlocks
	in deadlocks := (d+1, (!taken,steps)::dl);
	
	taken := steps
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> taken := steps
  done;
  if Options.int_brab_quiet then 
  Format.eprintf "Accepted: %d, Rejected: %d@." !accept !reject
  

let analyse_runs matrix =
    Hashtbl.fold (fun key el acc ->
      let taken_count = List.length el.taken_transitions in
      if taken_count = el.exit_number then acc
      else
	(key, el)::acc) initial_data []


let smart_run glob tsys trans procs depth=
  (*tsys is Ast.transition_info*)
  (*Random.self_init ();*)
  let transition_list = all_possible_transitions glob trans procs false in
  let transitions = ref (Array.of_list (transition_list))
  in

  let initial_runs = Array.length !transitions in 
  let transition_depth = List.length tsys in (*if possible max times to let proc follow itself*)
  let system_procs = (Options.get_interpret_procs ())  in
  let max_depth = transition_depth * system_procs *system_procs  in (* reflect on that*)
  
  Format.eprintf "Transitions: overall:%d -- initially:%d@." transition_depth initial_runs;
  Array.iter (fun (x,p) -> Format.eprintf "exits: %a(%a)@." Hstring.print x.tr_name Variable.print_vars p) !transitions;


  (*
    Initial Run
    Run a X times from Init, each time taking a different first step. 
    First basic statistics exploration. 
  *)

  let matrix = create_transition_hash tsys in
  let possibility_matrix = create_transition_hash tsys in 

  
  List.iter (fun (tran, pro) ->
    let env = apply_transition pro tran.tr_name trans glob in
    markov_init_run env tsys procs trans max_depth matrix possibility_matrix) transition_list ;

  List.iter (fun p ->
    force_procs_forward glob trans procs max_depth p ) procs ;
  
(*
  Hashtbl.iter (fun key el ->
    Format.eprintf "---------------------------:@.";
    (*Format.eprintf "Env: %a@." print_interpret_env el.state;*)
    Format.eprintf "Seen: %d\n\
                    Exits: %d\n\
                    Remaining:%d@." el.seen el.exit_number (List.length el.exit_transitions);
    List.iter (fun (x,l) -> Format.eprintf "%a(%a)@." Hstring.print x Variable.print_vars l) el.exit_transitions;
    Format.eprintf "Taken:@.";
    List.iter (fun (x,l) -> Format.eprintf "%a(%a)@." Hstring.print x Variable.print_vars l) el.taken_transitions 

  ) initial_data;


  Hashtbl.iter (fun key el -> Format.eprintf "%a ---- %d@." Hstring.print key el) initial_tr_count;*)




  
  let initD = Hashtbl.fold (fun k el acc -> (env_to_satom_map el.state)::acc ) initial_data [] in
  Format.eprintf "Seen%d@." (List.length initD);

  
  visited_states := initD @ !visited_states
    
  
  
  

  
  

  
 


    


let markov_entropy_detailed2 glob tsys all_procs trans steps det_flag=
  (*Random.self_init ();*)
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
    




let execute_random_forward glob_env trans all_procs unsafe depth curr_round=
  let steps = ref 0 in
  (*Random.self_init ();*)
  let running_env = ref glob_env in
  let transitions = ref (Array.of_list (all_possible_transitions glob_env trans all_procs false)) in 
  let queue = ref PersistentQueue.empty in 
  while !steps < depth do
    incr overall;

    (*let saa = env_to_satom !running_env in
    let saa_map = List.rev (extract_procs saa) in
    let map1 = gen_mapping saa_map in
    let mm = SAtom.subst map1 saa in
    Format.eprintf "Map 1@.";
    List.iter (fun (x,y) -> Format.eprintf "%a ---> %a@." Hstring.print x Hstring.print y) map1;
    Format.eprintf "System Map@.";
    List.iter (fun (x,y) -> Format.eprintf "%a ---> %a@." Hstring.print x Hstring.print y) !system_sigma_en;

    Format.eprintf "Original env: %a@." SAtom.print saa;

    let env_mapped = SAtom.subst !system_sigma_en mm in

    Format.eprintf "Mapped env: %a@." SAtom.print env_mapped;


    
    begin
      try
	let he  = Hashtbl.find hSCount env_mapped in
	Hashtbl.replace hSCount env_mapped (he+1)
      with Not_found ->
	begin
	  Hashtbl.add hSCount env_mapped 1;
	  let ee = env_to_map env_mapped in
	  visited_states := ee::!visited_states;
	  incr visit_count;
	end
    end;

    let hash = hash_full_env !running_env in
    begin
      try
	let he,ee = Hashtbl.find hCount hash in
	Hashtbl.replace hCount hash ((he+1),ee)
      with Not_found ->
	begin
	  Hashtbl.add hCount hash (1,!running_env);
	  (*let ee = env_to_satom_map !running_env in
	  visited_states := ee::!visited_states;
	  incr visit_count;*)
	end
    end;*)
    
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
      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (apply,apply_procs) = !transitions.(rand) in
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in
      begin
	try 
	  let ht_count, seen = Hashtbl.find tr_count apply.tr_name in
	  let seen = if seen = -1 then curr_round else seen in  
	  Hashtbl.replace tr_count apply.tr_name (ht_count+1,seen )
	with Not_found ->  Hashtbl.add tr_count apply.tr_name (1, curr_round)
      end;
      queue := PersistentQueue.push (apply.tr_name, apply_procs) !queue;
      (*check_unsafe new_env unsafe;*)
      running_env := new_env;
      incr steps;
      transitions := Array.of_list (all_possible_transitions !running_env trans all_procs true);
      (*count seen states*)
      
    with
      | TopError Deadlock ->
	let d,dl =  !deadlocks
	in deadlocks := (d+1, (!steps,depth)::dl);
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
	Format.printf "%a@." print_forward_trace !queue
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
  (*Random.self_init ();*)
  let orig_count = count in 
  let depths = ref [] in 
  let rec aux count  =
    match count with
      | 0 ->

	List.iter (fun x ->
	  Format.eprintf "---------------------------@.";
	  STMap.iter (fun key el ->
	    Format.eprintf "%a = %a@." Term.print key Term.print el)x) !visited_states;
	
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
	let max_dl, dl = !deadlocks in
	Format.printf "Deadlocked %d/%d times@." max_dl orig_count;
	if Options.int_deadlock then
	  List.iter (fun (x,y) -> Format.printf "Step %d / %d@." x y) dl; 
	Format.printf "%a" Pretty.print_line ();
	Format.printf "Transition statistics:@.";
	Hashtbl.iter (fun key (el,seen) ->
	  Format.printf "%a : %d times" Hstring.print key el;
	  if seen = -1 then Format.printf "[]@."
	  else Format.printf " [first seen: round %d]@." seen	    
	) tr_count;
	Format.printf "\n%a" Pretty.print_double_line ();
	if Options.int_brab_quiet then
	  begin
	    Format.printf "Various depths:@.";
	    List.iter (fun x -> Format.printf " %d" x) !depths;
	    Format.printf "@."
	  end 
      | _ ->
	let rand = (Random.int depth) + 1 in
	depths := rand :: !depths;
	execute_random_forward env trans procs unsafe depth (orig_count - count);
	aux (count-1)
  in
  aux count


let run_markov env tsys trans procs unsafe count depth =
  (*Random.self_init ();*)
  let orig_count = count in 
  let depths = ref [] in 
  let rec aux count  =
    match count with
      | 0 ->
	let stats = Hashtbl.stats hCount in
	Format.printf "\n%a" Pretty.print_double_line ();
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
	let max_dl, dl = !deadlocks in
	Format.printf "Deadlocked %d/%d times@." max_dl orig_count;
	if Options.int_deadlock then
	  List.iter (fun (x,y) -> Format.printf "Step %d / %d@." x y) dl;
	Format.printf "%a" Pretty.print_line ();
	Format.printf "Transition statistics:@.";
	Hashtbl.iter (fun key (el,seen) ->
	  Format.printf "%a : %d times" Hstring.print key el;
	  if seen = -1 then Format.printf "[]@."
	  else Format.printf " [first seen: round %d]@." seen	    
	) tr_count;
	Format.printf "\n%a" Pretty.print_double_line ();
	if Options.int_brab_quiet then
	  begin
	    Format.printf "Various depths:@.";
	    List.iter (fun x -> Format.printf " %d" x) !depths;
	    Format.printf "@."
	  end 
      | _ ->
	let rand = (Random.int depth) + 1 in
	depths := rand :: !depths;
	markov_entropy_detailed env tsys procs trans rand (orig_count - count);
	aux (count-1)
  in
  aux count    



    

let throwaway = Elem(Hstring.make "UNDEF", Glob)


let init tsys =
  Random.self_init ();
  Sys.catch_break true;
  let fmt = Format.std_formatter in
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
  (*let original_init = Env.fold (fun k x acc ->
    if Term.compare x throwaway = 0 then
      acc
    else Env.add k x acc) env Env.empty  in
  let original_init = env_to_satom_map (original_init, 0,0,0) in
  visited_states := original_init :: !visited_states;*)

  let env_final, original_init =
      Env.fold (fun k x (env_acc,v_acc) ->
	if Term.compare x throwaway = 0 then
	  begin
	    match k with 
	      | Elem(n,_) | Access(n,_) -> 
		let _, ty = Smt.Symbol.type_of n in
		(Env.add k {value = random_value ty; typ = ty } env_acc, v_acc)
		(*(env_acc, v_acc)*)
	  |  _ -> assert false	
	end
      else
	begin
	  match k with
	    | Elem(n, _) | Access(n, _) ->  
	      let _, ty = Smt.Symbol.type_of n in
	      if is_semaphore ty then
		begin
		  let temp = {value = semaphore_init x; typ = ty}
		  in
		  Env.add k temp env_acc, Env.add k temp v_acc
		end 
	      else 
		  begin
		    let temp = {value = cub_to_val x ; typ = ty }
		    in Env.add k temp env_acc, Env.add k temp v_acc
		  end
	    | _ -> assert false

	end
      ) env (Env.empty, Env.empty) in
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
  let orig_init =
    Env.mapi (fun k x ->
      match x.value with
	| VArith ta -> let v = eval_arith ta env_final x.typ in
		       {value =  v; typ = x.typ}
	| _ ->
	  x


    ) original_init in

  visited_states := (env_to_satom_map (orig_init,0,0,0)) :: !visited_states;
  
  let env_final =
    List.fold_left (fun acc x ->
      Env.add (Elem(x, Var)) {value = VAlive; typ = ty_proc} acc
  ) env_final procs
  in
  
  let t_transitions = List.map (fun x -> x.tr_info) tsys.t_trans in 
  let transitions =
    List.fold_left ( fun acc t ->    
      Trans.add t.tr_name t acc ) Trans.empty t_transitions in
  List.iter (fun x -> Hashtbl.add tr_count x.tr_name (0, -1) )t_transitions;
  let original_env = env_final, lock_queue, cond_sets, semaphores in 
  let unsafe = List.map (fun x -> 0,x.cube.vars ,x.cube.litterals) tsys.t_unsafe in
  let unsafe = init_unsafe procs unsafe in

  

  if Options.mrkv_brab = 1 then
    run_markov original_env t_transitions transitions procs unsafe Options.rounds Options.depth_ib
  else if Options.mrkv_brab = 0 then 
    run original_env transitions procs unsafe Options.rounds Options.depth_ib
  else
    smart_run original_env t_transitions transitions procs Options.depth_ib
  (*List.iter (fun x -> Format.eprintf "======\nNEW ENV@.";

    STMap.iter (fun key el -> Format.eprintf "%a = %a@." Term.print key Term.print el) x) !visited_states
  *)

  
  

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



let test_vals op v1 v2 =
  match op with
    | Eq -> Term.compare v1 v2 = 0    
    | Neq -> Term.compare v1 v2 <> 0 
    | Lt -> Term.compare v1 v2 = -1 
    | Le -> Term.compare v1 v2 = -1 || Term.compare v1 v2 = 0



let test_cands cands =
  (*List.iter (fun x -> Format.eprintf "CANDS:%a @." Node.print x) cands;*)
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
		  try
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
			      (*Format.eprintf "t1 %a v1 is %a\nt2 %av2 is %a@."
				Term.print t1 Term.print v1 Term.print t2 Term.print v2;


			      Format.eprintf "My candidate: %a@." Node.print node;*)
			      
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
		  with
		    | Not_found -> true::flagL
		      
		) nlitts []
	      in
	      (List.for_all (fun x -> x) f)::acc
	    ) [] cands
	  in
	  
	  let rec temp l ff=
	    match l with
		| [] -> ff
		| hd::tl -> if hd then false else temp tl ff
			   (*if hd then temp tl (false&&ff) else temp tl ff*)			  
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
  (*Format.eprintf "candidates: @.";
  List.iter (fun x -> Format.eprintf  "%a@." Node.print x ) n;*)
  
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
      (*Format.eprintf "LOOK what I picked mom! %a@." Node.print l;*)
      Some (l)


let first_good_candid2ate n =
  let num_procs = Options.int_brab in
  let procs = Variable.give_procs num_procs in
  let cands =
    List.fold_left (fun acc s ->
      let d = List.rev (Variable.all_permutations (Node.variables s) procs)
      in
      let cands = 
	List.fold_left (fun acc sigma ->
	  (Node.create ~kind:Approx (Cube.subst sigma s.cube))::acc)[] d
      in
      (*List.iter (fun x -> Format.eprintf "Candidate: %a@." Node.print x) cands;*)
      try
	let res = test_cands cands in
	if res = None then acc else assert false
      with
	| OKCands rem ->  rem::acc
    ) [] n   
  in
  if cands = [] then None
  else
  let cand = List.rev cands in
  let cand = List.hd (List.hd cand) in
  Some cand

