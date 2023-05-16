open Interpret_calc
open Interpret_types
open Interpret_errors
open Ast
open Types


(*  val init : Ast.t_system -> unit
    (** Initialize the oracle on a given system *)

    val first_good_candidate : Node.t list -> Node.t option 
    (** Given a list of candidate invariants, returns the first one that seems
        to be indeed an invariant. *)
end*)
 
let visited_states = ref []
let visit_count = ref 0
let overall = ref 0
let hCount = Hashtbl.create 100
let hSCount = Hashtbl.create 100

let system_sigma_en = ref []
let system_sigma_de = ref []
let tr_count = Hashtbl.create 10
let deadlocks = ref (0, [])

  
module STMap = Map.Make (Types.Term)

module ExitMap = Map.Make (struct type t =  Hstring.t * Variable.t list
				  let compare (h,vl) (h2, vl2) =
				    let c = Hstring.compare h h2 in
				    if c = 0 then 
				      Variable.compare_list vl vl2 
				    else c
end)
  
type data = {
  state : Interpret_types.global;
  seen : int;
  exit_number : int;
  exit_transitions : (Hstring.t * Variable.t list) list ;
  exit_remaining : (Hstring.t * Variable.t list) list ;
  taken_transitions : int ExitMap.t;
}


type deadlock_state = {
  dead_state : Interpret_types.global;
  dead_predecessor : Interpret_types.global;
  dead_path : (Hstring.t * Variable.t list) PersistentQueue.t;
  dead_steps : int
}


let install_sigint () =
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ ->
         Format.printf "\n@{<b>@{<fg_magenta>Stopping search@}@}@.";
         raise Exit
       ))


let print_transitions fmt t =
  List.iter (fun (x, y) -> Format.printf "%a(%a); " Hstring.print x Variable.print_vars y) t


let print_exit_map fmt t =
  ExitMap.iter (fun (x,y) d -> Format.printf "%a(%a) : %d times; %!" Hstring.print x Variable.print_vars y d) t
    
let print_stateless_data fmt data =
  Format.printf "{ seen: %d;\n\
                   exit_number: %d;\n\
                   exit_transitions: %a\n\
                   exit_remaining: %a\n\
                   taken_transitions: %a }@."
    data.seen
    data.exit_number
    print_transitions data.exit_transitions
    print_transitions data.exit_remaining
    print_exit_map data.taken_transitions

    
let print_data fmt data =
  Format.printf "{ state: %a;\n\
                   seen: %d;\n\
                   exit_number: %d;\n\
                   exit_transitions: %a\n\
                   exit_remaining: %a\n\
                   taken_transitions: %a }@."
    print_interpret_env data.state
    data.seen
    data.exit_number
    print_transitions data.exit_transitions
    print_transitions data.exit_remaining
    print_exit_map data.taken_transitions
    
    
    
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


let fuzzy_visited = Hashtbl.create 200

let bfs_visited = Hashtbl.create 200
let fuzz_tr_count = Hashtbl.create 50
let remaining_pool = Hashtbl.create 200
let pool_size = ref 0 
  
let fresh = 
  let cpt = ref 0 in
  fun () -> incr cpt; !cpt

  
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
  

let least_taken_exit s =
  let exits = s.taken_transitions in
  let first = ExitMap.choose exits in 
  ExitMap.fold (fun key el (k,acc) ->
    if el < acc then (key,el) else (k,acc)) exits first
  

let env_to_satom_map (env,_,_,_) =
  Env.fold (fun key {value = el} acc ->
    match el with
      | VGlob el -> (*assert false*) STMap.add key (Elem(el, Glob)) acc
      | VProc el -> STMap.add key (Elem(el, Var)) acc 
      | VConstr el -> STMap.add key (Elem(el, Constr)) acc
      | VAccess(el,vl) -> Format.eprintf "wtf: %a, %a@." Hstring.print el Variable.print_vars vl;assert false
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

exception Dead of int

    
let force_procs_forward code glob_env trans all_procs p_proc all_unsafes =
  let depth = Random.int 100 in
  let steps = ref 0 in
  let running_env = ref glob_env.state in
  let transitions = ref  (all_possible_transitions glob_env.state trans all_procs false) in 
  let old_hash = ref (hash_full_env glob_env.state) in
  let rem_pool = ref 0 in
  let add_pool = ref 0 in 
  let new_seen = ref 0 in
  let old_pool = ref !pool_size in
  let old_code = ref code in
  while !steps < depth do
    incr overall;
    try
      if (List.length !visited_states) > Options.fuzz_s then
      begin
	Format.printf "\n\nSet limit reached@."; raise Exit
      end;

      let tr_with_proc = choose_current_proc_list p_proc !transitions in
      let choose_from =
	if tr_with_proc = []
	then 
	  Array.of_list (!transitions)
	else Array.of_list (tr_with_proc) in     
      let l = Array.length choose_from in
      if l = 0 then raise (Dead !old_hash);
      let rand = Random.int l in
      let (apply,apply_procs) = choose_from.(rand) in
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in
      if !steps > 0 then
	begin
	  try
	    let data = Hashtbl.find bfs_visited !old_hash in
	    let new_map =
	      try
		ExitMap.find (apply.tr_name, apply_procs) data.taken_transitions
	      with
		  Not_found -> 0 
	    in
	    let rem = List.filter (fun x ->
		  not (compare_exits x (apply.tr_name, apply_procs))
		) data.exit_remaining in
	    Hashtbl.replace bfs_visited !old_hash
	      { state = data.state;
		seen = data.seen;
		exit_number = data.exit_number;
		exit_transitions = data.exit_transitions;
		exit_remaining = rem;
		taken_transitions =
		  ExitMap.add (apply.tr_name, apply_procs) (new_map+1) data.taken_transitions;
		
	      };
	      if (List.length rem) = 0 && (!old_pool < !pool_size) then
		begin
		  Hashtbl.remove remaining_pool !old_code;
	      decr pool_size;
	      incr rem_pool;
	    end 
	  with Not_found -> assert false
	end ;
      let hash = hash_full_env new_env in    
      let exits = all_possible_transitions new_env trans all_procs true in

      begin
	try
	  let ndata = Hashtbl.find bfs_visited hash in
	  Hashtbl.replace bfs_visited hash
	  { state = ndata.state;
	      seen = ndata.seen + 1 ;
	      exit_number = ndata.exit_number;
	      exit_transitions = ndata.exit_transitions;
	      exit_remaining = ndata.exit_remaining;
	      taken_transitions = ndata.taken_transitions };
	    
	with Not_found ->
	  incr visit_count;
	  incr new_seen;
	  let mapped_exits = List.map (fun (x,y) -> (x.tr_name, y)) exits in
	  let nd = 
	    { state = new_env;
	      seen = 0 ;
	      exit_number = List.length exits;
	      exit_transitions = mapped_exits;
	      exit_remaining = mapped_exits;
	      taken_transitions = ExitMap.empty;    
	    }
	  in  Hashtbl.add bfs_visited hash nd;

	  begin
	    try
	      check_unsafe new_env all_unsafes;
	    with
	      | TopError Unsafe ->
		Format.printf "\n@{<b>@{<bg_red>WARNING@}@}";
		Format.printf "@{<fg_red> Unsafe state reached during forward exploration@}@."
	  end;
	  if (List.length exits) > 1 && (!steps < depth - 2) then
	    begin
	      let f = fresh () in
	      old_code := f; 
	      Hashtbl.add remaining_pool f nd;
	      old_pool := !pool_size; 
	      incr pool_size;
	      incr add_pool;
	    end;
      end;
      
      begin
	try 
	  let ht_count = Hashtbl.find fuzz_tr_count apply.tr_name in
	  Hashtbl.replace fuzz_tr_count apply.tr_name (ht_count+1)
	    with Not_found ->  Hashtbl.add fuzz_tr_count apply.tr_name 1
      end;
      (*check_unsafe new_env unsafe;*)
      old_hash := hash;
      running_env := new_env;
      incr steps;
      transitions := exits;
      (*count seen states*)
    with
      | Dead h ->
	Format.printf "Deadlock reached.";
	steps := depth
      | Stdlib.Sys.Break | Exit ->  steps := depth; raise Exit
  done ;
  Format.printf "Force proc: new states seen: %d. New added to pool: %d Removed from pool %d@." !new_seen !add_pool !rem_pool


let markov_entropy code glob all_procs trans =
  Random.self_init ();
  let taken = ref 0 in
  let new_seen = ref 0 in
  let transitions = ref (Array.of_list (all_possible_transitions glob.state trans all_procs false))
  in
  let steps = Random.int 1000 in
  Format.printf "Chose Markov for a depth of %d steps@." steps; 
  let pool = ref 0 in
  let rem_pool = ref 0 in 
  let running_env = ref glob.state in
  let accept = ref 0  in
  let reject = ref 0 in
  let old_code = ref code in 
  let old_hash = ref (hash_full_env glob.state) in
  let old_pool = ref !pool_size in 
  let w1 = ref (entropy_env glob.state trans all_procs) in 
  while !taken < steps do
    try
      if (!visit_count) > Options.fuzz_s then
      begin
	Format.printf "\n\nSet limit reached@."; raise Exit
      end;

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
	  
	  begin
	    try
	      let data = Hashtbl.find bfs_visited !old_hash in
	      let new_map =
		try
		  ExitMap.find (proposal.tr_name, prop_procs) data.taken_transitions
		with
		    Not_found -> 0 
	      in
	      let rem = List.filter (fun x ->
		not (compare_exits x (proposal.tr_name, prop_procs))
	      ) data.exit_remaining in
	      
	      Hashtbl.replace bfs_visited !old_hash 
		{ state = data.state;
		  seen = data.seen;
		  exit_number = data.exit_number;
		  exit_transitions = data.exit_transitions;
		  exit_remaining = rem;
		  taken_transitions =
		    ExitMap.add (proposal.tr_name, prop_procs) (new_map+1) data.taken_transitions;};
	      if (List.length rem) = 0 && (!old_pool < !pool_size) then
		begin
		  Hashtbl.remove remaining_pool !old_code;
		  decr pool_size;
		  incr rem_pool;
		end 
	    with Not_found -> assert false 
	  end;

	  
	  let exits = all_possible_transitions temp_env trans all_procs true in

	  begin
	    try
	      let c_t =
		Hashtbl.find fuzz_tr_count proposal.tr_name in
              Hashtbl.replace fuzz_tr_count proposal.tr_name (c_t+1)
	    with Not_found -> Hashtbl.add fuzz_tr_count proposal.tr_name 1
	  end ;
	  
	  let hash = hash_full_env temp_env in

	  begin
	    try
	      let ndata = Hashtbl.find bfs_visited hash in
	      Hashtbl.replace bfs_visited hash
		{ state = ndata.state;
		  seen = ndata.seen + 1 ;
		  exit_number = ndata.exit_number;
		  exit_transitions = ndata.exit_transitions;
		  exit_remaining = ndata.exit_remaining;
		  taken_transitions = ndata.taken_transitions };
	    with Not_found -> 
	     begin
		let mapped_exits = List.map (fun (x,y) -> (x.tr_name, y)) exits in
		let nd =
		  { state = temp_env;
		    seen = 1;
		    exit_number = List.length exits;
		    exit_transitions = mapped_exits;
		    exit_remaining = mapped_exits;
		    taken_transitions = ExitMap.empty; } in
		Hashtbl.add bfs_visited hash nd;
		incr new_seen;
		let e_m = env_to_satom_map temp_env in
		visited_states := e_m::!visited_states;
		incr visit_count;
		if (List.length exits) > 1 then
		  begin
		    let f = fresh () in
		    old_code := f; 
		    Hashtbl.add remaining_pool f nd;
		    old_pool := !pool_size; 
		    incr pool_size;
		    incr pool;
		  end 
		
	      end  

	  end;	  
	  transitions := Array.of_list (exits);
	  incr accept;
	  w1 := w2;
	  running_env := temp_env;
	  incr taken; 
	  old_hash := hash;
	end
      else
	begin
	  incr reject
	end(*;
      incr taken*)
    with
      | TopError Deadlock ->	
	taken := steps
      | Stdlib.Sys.Break | Stdlib.Exit ->
	if Options.int_brab_quiet then 
	  Format.eprintf "Accepted: %d, Rejected: %d@." !accept !reject;
	raise Exit	
  done;
  Format.printf "Markov: new seen states: %d, added to pool: %d, Removed from pool %d@." !new_seen !pool !rem_pool
  



  

let count_exit_system () =
  Hashtbl.fold (fun key el (acc, tposs_count, taken_count) ->
    let card = ExitMap.cardinal el.taken_transitions in
      if card = el.exit_number
      then (acc, tposs_count + card, taken_count + card)
      else if card < el.exit_number then
      	  ((key, el)::acc, tposs_count + el.exit_number, taken_count + card) 
       else assert false	
    ) initial_data ([],0,0)

let count_hit_transitions () =
  Hashtbl.fold (fun k el (acc, count) ->
    if el > 0 then (k::acc, count+1) else (acc,count)) initial_tr_count ([],0)



    
let analyse_runs matrix =
  Hashtbl.fold (fun key el acc ->
    let card = ExitMap.cardinal el.taken_transitions in
      if card = el.exit_number
      then acc
      else if card < el.exit_number then
      	  (key, el)::acc
       else assert false	
    ) initial_data []




(*
1. choisit un candidat au hasard (mais biaisé vers ceux pas encore fuzzés)
2. t' <- t
3. n fois (n étant calculé avec une fonction en fonction de je sais plus quoi)
    a. i fois (i = rand(2, 4, 8, 16, 32, 64, 128))
        + choisir une position de t'
        + choisir une mutation
        + appliquer la mutation a la position sur t'
    b. executer t'
    c. si nouvelle coverage
         + break
    d. t' <- t 




*)
   

let change_proc proc =
  let proc = Variable.number proc in
  let new_proc = (proc mod (Options.get_interpret_procs ())) + 1 in
  Hstring.make ("#"^ (string_of_int new_proc))
			       
let pick_transition_different transitions current num_t =
  let rec choose () =
    let rand = Random.int num_t in
    let chosen = transitions.(rand) in
    if Hstring.equal current chosen then choose ()
    else chosen
  in choose ()

(*let pick_transition transitions current num_t =
  let rand = Random.int num_t in
  transitions.(rand)*) 
    
let mutate_proc_no_transition candidate steps  =
  let change = Random.int steps in
  let chosen_tr, chosen_procs = candidate.(change) in
  let new_procs = List.map (fun p -> change_proc p) chosen_procs in
  candidate.(change) <- chosen_tr,new_procs

let mutate_proc (trans,procs)=
  let new_procs = List.map (fun p -> change_proc p) procs in
  trans,new_procs

let mutate_transitions_no_transition candidate steps transitions num_t =
  let change = Random.int steps in
  let chosen_tr, chosen_procs = candidate.(change) in
  let len_procs = List.length chosen_procs in
  let choose_from = Array.fold_left (fun acc (x,el) ->
    if List.length el = len_procs then (x,el)::acc else acc )[]  transitions in
  let choose_from = Array.of_list choose_from in
  let choose_length = Array.length choose_from in 
  let new_transition = choose_from.(Random.int choose_length)  in
  candidate.(change) <- new_transition


let mutate_transition transitions num_t (current,current_procs) = (*try to keep procs*)
  let len_current = List.length current_procs in
  let l_suggestions, sug_count =
    Array.fold_left (fun (acc,count) (x,y) ->
      if List.length y = len_current &&
	(Hstring.compare x current <> 0)
      then (x,y)::acc,count+1
      else acc,count)
      ([],0) transitions in
  if sug_count = 0 then current, current_procs
  else
    begin
      let suggestions = Array.of_list l_suggestions in
      let sug = Random.int sug_count in
      let _, procs = suggestions.(sug) in
      current, procs
    end 
  

let mutate_step_no_transition candidate steps transitions num_t = 
  let change = Random.int steps in
  let replace = Random.int num_t in
  candidate.(change) <- transitions.(replace)
    
let mutate_step transitions num_t = 
  let change = Random.int num_t in
  transitions.(change)

let mutate_random_replace candidate steps transitions num_t=
  let rand = Random.int steps in
  let rec aux count =
    match count with
      | 0 -> ()
      | _ -> mutate_step candidate steps transitions num_t; aux (count -1)
  in
  aux rand
  
let mutate_shorten candidate steps =
  let pos = Random.int steps in
  let len = Random.int (steps - pos) in
  Array.sub candidate pos len

let dead_mutation candidate step transitions num_t =
  let rand = Random.int num_t in
  candidate.(step) <- transitions.(rand)

let mutate_candidate candidate steps (dead,ds) all_tr length_tr = assert false
  (*if dead then
    begin
      dead_mutation candidate ds all_tr length_tr;
      None
    end 
  else 
    begin
      let r = Random.int 4 in
      match r with
	| 0 -> mutate_proc candidate steps; None
	| 1 -> mutate_transitions candidate steps all_tr length_tr; None
	| 2 -> mutate_step candidate steps all_tr length_tr; None 
	| 3 -> mutate_random_replace candidate steps all_tr length_tr; None
	(*| 4 -> Some (mutate_shorten candidate steps)*)
	| _ -> assert false
    end *)


let lengthen_candidate_old all_tr length_tr =
  let rand = Array.make (Random.int 100) (Hstring.make "", []) in
  Array.map (fun el -> all_tr.(Random.int length_tr) )rand
  

(*let mutate_me step all_tr length_tr =
  let i = (Random.int 100) mod 3 in 
  match i with
    | 0 -> mutate_proc step
    | 1 -> mutate_transition all_tr length_tr step
    | 2 -> mutate_step all_tr length_tr
  | _ -> assert false*)

let mutate_me step all_tr length_tr = assert false

   

let mutate_lengthen_rerun candidate all_tr length_tr depth = assert false 
 


let i_mutations i candidate depth (dead,ds) all_tr length_tr  =
  let depth = if dead then ds else depth in
  let rec mutate count cand dep =
    match count with
      | 0 -> cand
      | _ ->
	let s_cand =
	  mutate_candidate cand dep (dead,ds) all_tr length_tr  in
        begin
	  match s_cand with
	    | None -> let d = if dead then ds else dep in mutate (count -1) cand d
	    | Some s -> let d = if dead then ds else dep in mutate (count -1) s d
	end 
  in mutate i candidate depth

(*let n_mutate_tests
    n candidate glob_env all_procs trans depth all_tr length_tr all_unsafes=
  let times = [|2; 4; 8; 16; 32; 64; 128|] in
  let rec mut_test count cand (dead,ds)  =
    match count with
      | 0 -> false, cand
      | _ ->
	let rand_iterations = times.(Random.int 7) in 
	let candi = i_mutations rand_iterations cand depth (dead,ds) all_tr length_tr in
	let steps, died, coverage = apply_seed glob_env trans all_procs  candi all_unsafes in
	if coverage > 0 then (true,candi)
	else mut_test (count-1) candidate (died,steps)
  in
  mut_test n (Array.copy candidate) (false,0)


let n_mutate_tests2 n candidate glob_env all_procs trans depth all_tr length_tr all_unsafes =
  let rec aux count =
    let c = Array.copy candidate in 
    let cand =
      Array.map (fun el -> if (Random.bool ()) then all_tr.(Random.int length_tr) else el) c in 
    let steps, died, coverage = apply_seed glob_env trans all_procs  cand all_unsafes in
    if coverage > 0 then true, cand
    else if count > 10000 then false, candidate
    else aux  (count +1)
  in aux 0

let n_mutate_tests3 n candidate glob_env all_procs trans depth all_tr length_tr all_unsafes=
  let rec aux count =
    let c = Array.copy candidate in
    let cand =
    if Random.bool () then
	  Array.map (fun el ->
	    if (Random.bool ()) then
	      mutate_me el all_tr length_tr
	    else el) c
    else
      Array.append c (lengthen_candidate all_tr length_tr) 
    in 
    let steps, died, coverage = apply_seed glob_env trans all_procs cand all_unsafes in
    if coverage > 0 then true, cand
    else if count > 10000 then false, candidate
    else aux  (count +1)
  in aux 0*)



  
  


(*let finish_queue queue =
  Queue.iter (fun (_,_, el) -> incr pool_size; Hashtbl.add remaining_pool (fresh ()) el) queue*)
	

let finish_queue queue trans all_procs=
  Queue.iter (fun (_,_, el) -> incr pool_size;
    let poss = all_possible_transitions el trans all_procs false in
    let l = List.length poss in
    let mapped_exits = List.map (fun (x,y) -> (x.tr_name, y)) poss in 
    let s= { state = el;
	     seen = 1;
	     exit_number = l;
	     exit_transitions = mapped_exits;
	     exit_remaining = mapped_exits;
	     taken_transitions = ExitMap.empty }
    in
    Hashtbl.add remaining_pool (fresh ()) s) queue

let reconstruct_trace parents me =
  let trace = ref [] in
  let bad = ref me in
  let not_init = ref true in
  while !not_init do
    let am_init, tr, h, e = Hashtbl.find parents !bad in
    if am_init then not_init := false
    else
      begin
	match tr with
	  | Some (t,tr_pr) -> trace := (t.tr_name,tr_pr)::!trace; bad := h
	  | None -> assert false
      end
  done;
  Format.printf "@{<fg_red>Error trace@}: ";
  Format.printf "Init";
  List.iter (fun (x,y) -> Format.printf " -> %a(%a)" Hstring.print x Variable.print_vars y) !trace;
  Format.printf " -> @{<fg_magenta>unsafe@}@."

exception ReachedUnsafe
exception NeverSeen of Interpret_types.global * (Ast.transition_info * Variable.t list) * int
exception StopExit


let grade_exits s tr tr_p =
  let rem = List.length s.exit_remaining in
  if rem = 0 then -100 
  else
    begin
      try
	let n =
	  ExitMap.find (tr.tr_name, tr_p) s.taken_transitions
	in
	let (sm,(mt,mp)) =
	  ExitMap.fold (fun k el (acc,t) -> if el < acc
	    then (el, k) else (acc, t)) s.taken_transitions (n, (tr.tr_name, tr_p))
	in
	if Hstring.equal mt tr.tr_name && (Hstring.compare_list mp tr_p = 0) then 50
	else 25 
      with Not_found -> 100 
    end 

    
(*let grade_state state tr tr_p =
  let exit_g = grade_exits state tr tr_p in*)
  
      
    

let grade_seen state_hash =
  try
    let _ = Hashtbl.find bfs_visited state_hash in
    false
  with Not_found -> true 



let choose_random_of_equal l =
  let c = List.length l in
  if c = 1 then List.hd l
  else
    begin
      let l = Array.of_list l in
      Random.self_init ();
      let i = Random.int c in
      l.(i)
    end  
    

let run_smart code node all_procs trans unsafes =
  let max_depth = Random.int 100 in
  Format.printf "Chosen depth for smart run: %d@." max_depth;
  let steps = ref 0 in
  let new_seen = ref 0 in
  let add_pool = ref 0 in
  let rem_pool = ref 0 in 
  let old_hash = ref (hash_full_env node.state) in 
  let running_env = ref node.state in
  let old_code = ref code in
  let old_pool = ref !pool_size in
  let transitions =
    ref (Array.of_list (all_possible_transitions node.state trans all_procs false)) in
  while !steps < max_depth do
    try
      if (!visit_count) > Options.fuzz_s then
      begin
	Format.printf "\n\nSet limit reached@."; raise Exit
      end;

    let l = Array.length !transitions in
    if l = 0 then raise (TopError Deadlock);
    let _,most_interesting =
      try 
	Array.fold_left (fun (curr_max, acc) (tr, trp) ->
	  let temp = apply_transition trp tr.tr_name trans !running_env in
	  let hash = hash_full_env temp in
	  let s =
	    try
	      Hashtbl.find bfs_visited hash
	    with Not_found ->  raise (NeverSeen (temp, (tr,trp), hash))
	  in
	  let g = grade_exits s tr trp in
	  if g > curr_max then (g, [(tr,trp, temp,hash)])
	  else if g = curr_max then (g, (tr, trp,temp,hash)::acc)
	  else (curr_max, acc)
	) (0,[]) !transitions;
      with
	| NeverSeen(state, (tr,trp), h) -> 0, [(tr, trp, state, h)]
    in
    let apply, apply_procs, temp_env, hash = 
      if most_interesting = []
      then
      (*apply random transition*)
	begin
	  let r = Random.int l in
	  let a, ap = !transitions.(r) in
          let e = apply_transition ap a.tr_name trans !running_env
	  in a, ap, e, (hash_full_env e)
	end 
      else
	choose_random_of_equal most_interesting
    in

      begin
	try
	  let data = Hashtbl.find bfs_visited !old_hash in
	  let new_map =
	    try
	      ExitMap.find (apply.tr_name, apply_procs) data.taken_transitions
	    with
		Not_found -> 0 
	  in
	  let rem = List.filter (fun x ->
	    not (compare_exits x (apply.tr_name, apply_procs))
	  ) data.exit_remaining in
	  
	  Hashtbl.replace bfs_visited !old_hash 
	    { state = data.state;
	      seen = data.seen;
	      exit_number = data.exit_number;
	      exit_transitions = data.exit_transitions;
	      exit_remaining = rem;
	      taken_transitions =
		ExitMap.add (apply.tr_name, apply_procs) (new_map+1) data.taken_transitions;};
	  if (List.length rem) = 0 && (!old_pool < !pool_size) then
	    begin
	      Hashtbl.remove remaining_pool !old_code;
	      decr pool_size;
	      incr rem_pool;
	    end 
	with Not_found -> assert false 
      end ;
    
    begin
      try
	let c_t =
	  Hashtbl.find fuzz_tr_count apply.tr_name in
        Hashtbl.replace fuzz_tr_count apply.tr_name (c_t+1)
      with Not_found -> Hashtbl.add fuzz_tr_count apply.tr_name 1
    end ;

      

    let exits = all_possible_transitions temp_env trans all_procs true in

    begin
	try
	  let ndata = Hashtbl.find bfs_visited hash in
	  Hashtbl.replace bfs_visited hash
	    { state = ndata.state;
	      seen = ndata.seen + 1 ;
	      exit_number = ndata.exit_number;
	      exit_transitions = ndata.exit_transitions;
	      exit_remaining = ndata.exit_remaining;
	      taken_transitions = ndata.taken_transitions };
	with Not_found ->
	  begin
	    let mapped_exits = List.map (fun (x,y) -> (x.tr_name, y)) exits in
	    let nd =
	      { state = temp_env;
		seen = 1;
		exit_number = List.length exits;
		exit_transitions = mapped_exits;
		exit_remaining = mapped_exits;
		taken_transitions = ExitMap.empty; } in
	    Hashtbl.add bfs_visited hash nd;
	    incr new_seen;
	    let e_m = env_to_satom_map temp_env in
	    visited_states := e_m::!visited_states;
	    incr visit_count;
	    if (List.length exits) > 1 && (!steps < max_depth - 2)  then
	      begin
		let f = fresh () in
		old_code := f; 
		Hashtbl.add remaining_pool f nd;
		old_pool := !pool_size; 
		incr pool_size;
		incr add_pool;
		
	      end	
	  end 
    end ;

    old_hash := hash;
    running_env := temp_env;
    incr steps;
    transitions := Array.of_list exits;
    with
      | TopError Deadlock -> Format.printf "Deadlock reached."; steps := max_depth
      | Stdlib.Sys.Break | Exit ->  steps := max_depth; raise Exit
  done ;
  Format.printf "Smart states seen: %d. New added to pool: %d Removed from pool %d@." !new_seen !add_pool !rem_pool


  
let further_bfs code node transitions all_procs all_unsafes =
  try
    (*let parents = Hashtbl.create 200 in*)
    let max_depth = Random.int 5 in
    let curr_depth = ref 0 in
    let curr = ref 0 in
    let rem = ref 1 in
    let old_code = ref code in
    let new_seen = ref 0 in
    let new_pool = ref 0 in
    let old_pool = ref !pool_size in
    let rem_pool = ref 0 in 
    let time_limit = 5.0 in
    let to_do = Queue.create () in
    Queue.push ((hash_full_env node.state),0,node.state) to_do;
    let time = Unix.time () in
    while (!curr_depth < max_depth) &&
      (not (Queue.is_empty to_do)) &&
      ((Unix.time () -. time) < time_limit) do
      let _, env_d, env = Queue.pop to_do in
      let old_hash = hash_full_env env in
      let possible = all_possible_transitions env transitions all_procs false in
      decr rem;
      List.iter (fun (at,at_p) ->
	let e = apply_transition at_p at.tr_name transitions env in
	let he = hash_full_env e in

	begin
	  try
	    let data = Hashtbl.find bfs_visited old_hash in
	    let new_map =
	      try
		ExitMap.find (at.tr_name, at_p) data.taken_transitions
	      with
		  Not_found -> 0 
	    in
	    let rem = List.filter (fun x ->
	      not (compare_exits x (at.tr_name, at_p))
	    ) data.exit_remaining in
	    
	    Hashtbl.replace bfs_visited old_hash 
	      { state = data.state;
		seen = data.seen;
		exit_number = data.exit_number;
		exit_transitions = data.exit_transitions;
		exit_remaining = rem;
		taken_transitions =
		  ExitMap.add (at.tr_name, at_p) (new_map+1) data.taken_transitions;};
	    if (List.length rem) = 0 && (!old_pool < !pool_size) then
	      begin
		Hashtbl.remove remaining_pool !old_code;
		decr pool_size;
		incr rem_pool;
	      end 
	  with Not_found -> assert false 
	end ;

	begin
	  try
	    let c_t =
	      Hashtbl.find fuzz_tr_count at.tr_name in
            Hashtbl.replace fuzz_tr_count at.tr_name (c_t+1)
	  with Not_found -> Hashtbl.add fuzz_tr_count at.tr_name 1
	end ;

	let exits = all_possible_transitions e transitions all_procs true in
	begin
	try
	  let ndata = Hashtbl.find bfs_visited he in
	  Hashtbl.replace bfs_visited he
	    { state = ndata.state;
	      seen = ndata.seen + 1 ;
	      exit_number = ndata.exit_number;
	      exit_transitions = ndata.exit_transitions;
	      exit_remaining = ndata.exit_remaining;
	      taken_transitions = ndata.taken_transitions };
	with Not_found ->
	  begin
	    let mapped_exits = List.map (fun (x,y) -> (x.tr_name, y)) exits in
	    let nd =
	      { state = e;
		seen = 1;
		exit_number = List.length exits;
		exit_transitions = mapped_exits;
		exit_remaining = mapped_exits;
		taken_transitions = ExitMap.empty; } in
	    Hashtbl.add bfs_visited he nd;
	    incr new_seen;
	    let e_m = env_to_satom_map e in
	    
	    visited_states := e_m::!visited_states;
	    incr visit_count;
	    if (!visit_count) > Options.fuzz_s then
      begin
	Format.printf "\n\nSet limit reached@."; raise Exit
      end;

	    if (List.length exits) > 1 && (!curr_depth < max_depth - 2) then
	      begin
		let f = fresh () in
		old_code := f; 
		Hashtbl.add remaining_pool f nd;
		old_pool := !pool_size; 
		incr pool_size;
		incr new_pool;		
	      end;	
	    incr curr;
	    incr rem;
	    Queue.push (he,env_d + 1, e) to_do
	  end
	end 
	) possible;
      if env_d > !curr_depth then incr curr_depth    
    done;
    (*Queue.iter (fun (_,x) -> incr pool_size; Hashtbl.add remaining_pool (fresh ()) x) to_do;*)
    finish_queue to_do transitions all_procs;
    Format.printf "Further BFS: %d new states added to visited, %d added to remaining pool@." !curr !rem;
  with
    | Stdlib.Sys.Break | Exit -> raise Exit
    

    
let interpret_bfs original_env transitions all_procs all_unsafes =
  try
    let parents = Hashtbl.create 200 in
    let max_depth = Options.fuzz_d in
    let curr_depth = ref 0 in
    let node = ref 0 in
    let rem = ref 1 in
    let time_limit = float (Options.fuzz_t) in
    check_unsafe original_env all_unsafes;
    let he = hash_full_env original_env in
    let all_poss = all_possible_transitions original_env transitions all_procs false in
    let exit_poss = List.map (fun (x,y) -> x.tr_name, y) all_poss in 
    let hi =
      { state = original_env;
	seen = 1;
	exit_number = List.length all_poss;
	exit_transitions = exit_poss;
	exit_remaining = exit_poss;
	taken_transitions = ExitMap.empty } in 
    Hashtbl.add bfs_visited he hi;
    let to_do = Queue.create () in
    Queue.push (he, 0,original_env) to_do;
    Hashtbl.add parents he (true, None, he, original_env);
    Format.printf "[VISITED][REMAINING][DEPTH]@.";
    let time = Unix.time () in
    while (!curr_depth < max_depth) &&
      (not (Queue.is_empty to_do)) &&
      ((Unix.time () -. time) < time_limit) do
      let ha, env_d, env = Queue.pop to_do in
      decr rem;
      let possible = all_possible_transitions env transitions all_procs false in
      List.iter (fun (at,at_p) ->
	let e = apply_transition at_p at.tr_name transitions env in

	begin
	    try 
	      let ht_count = Hashtbl.find fuzz_tr_count at.tr_name in
	      Hashtbl.replace fuzz_tr_count at.tr_name (ht_count+1)
	    with Not_found ->  Hashtbl.add fuzz_tr_count at.tr_name 1
	  end;

	
	let he = hash_full_env e in
	try
	  let _ = Hashtbl.find bfs_visited he in
	  ()
	with Not_found ->
	  begin
	    let poss = all_possible_transitions e transitions all_procs false  in
	    let exits = List.map (fun (x,y) -> x.tr_name, y) poss in
	    let ev =
	      { state = e;
		seen = 1;
		exit_number = List.length poss;
		exit_transitions = exits;
		exit_remaining = exits;
		taken_transitions = ExitMap.empty}
	    in 		
	    Hashtbl.add bfs_visited he ev;
	    Hashtbl.add parents he (false, Some (at, at_p), ha, env);
	    begin
	      try
		check_unsafe e all_unsafes;
	      with
		| TopError Unsafe ->
		  Format.printf "\n@{<b>@{<bg_red>WARNING@}@}@.";
		  Format.printf "@{<fg_red>Unsafe state reached during forward exploration@}@.";
		  reconstruct_trace parents he;
		  raise ReachedUnsafe
	    end;
	    let e_m = env_to_satom_map e in
	    visited_states := e_m::!visited_states;
	    incr visit_count;
	    incr node;
	    incr rem;
	    Format.printf "[%d][%d][%d]\r%!" !node !rem env_d;
	    Queue.push (he, env_d + 1, e) to_do
	  end ) possible;
      if env_d > !curr_depth then incr curr_depth
    done;
    if not (Queue.is_empty to_do) then finish_queue to_do transitions all_procs
  with
    | Stdlib.Sys.Break | Exit -> ()
    | TopError Unsafe ->
      Format.printf "\n@{<b>@{<bg_red>WARNING@}@}@.";
      Format.printf "@{<b>@{<fg_red>Initial state is unsafe@}@}\n@.";
      raise Exit
      
      
      
  (*visited_states := !fuzzy_visited @ !visited_states*)
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


let run_forward code node all_procs trans unsafes =
  let max_depth = Random.int 1000 in
  Format.printf "Chosen depth for random: %d@." max_depth;
  let steps = ref 0 in
  let new_seen = ref 0 in
  let add_pool = ref 0 in
  let rem_pool = ref 0 in 
  let old_hash = ref (hash_full_env node.state) in 
  let running_env = ref node.state in
  let old_code = ref code in
  let old_pool = ref !pool_size in
  let transitions =
    ref (Array.of_list (all_possible_transitions node.state trans all_procs false)) in
  while !steps < max_depth do
    try
      if (!visit_count) > Options.fuzz_s then
      begin
	Format.printf "\n\nSet limit reached@."; raise Exit
      end;

      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (apply,apply_procs) = !transitions.(rand) in
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in
      let hash = hash_full_env new_env in
      begin
	try
	  let data = Hashtbl.find bfs_visited !old_hash in
	  let new_map =
	    try
	      ExitMap.find (apply.tr_name, apply_procs) data.taken_transitions
	    with
		Not_found -> 0 
	  in
	  let rem = List.filter (fun x ->
	    not (compare_exits x (apply.tr_name, apply_procs))
	  ) data.exit_remaining in
	  
	  Hashtbl.replace bfs_visited !old_hash 
	    { state = data.state;
	    seen = data.seen;
	    exit_number = data.exit_number;
	    exit_transitions = data.exit_transitions;
	    exit_remaining = rem;
	    taken_transitions =
	      ExitMap.add (apply.tr_name, apply_procs) (new_map+1) data.taken_transitions;};
	  if (List.length rem) = 0 && (!old_pool < !pool_size) then
	    begin
	      Hashtbl.remove remaining_pool !old_code;
	      decr pool_size;
	      incr rem_pool;
	    end 
	with Not_found -> assert false 
      end;

      begin
	try
	  let c_t =
	    Hashtbl.find fuzz_tr_count apply.tr_name in
          Hashtbl.replace fuzz_tr_count apply.tr_name (c_t+1)
	with Not_found -> Hashtbl.add fuzz_tr_count apply.tr_name 1
      end ;

      let exits = all_possible_transitions new_env trans all_procs true in

      begin
	try
	  let ndata = Hashtbl.find bfs_visited hash in
	  Hashtbl.replace bfs_visited hash
	    { state = ndata.state;
	      seen = ndata.seen + 1 ;
	      exit_number = ndata.exit_number;
	      exit_transitions = ndata.exit_transitions;
	      exit_remaining = ndata.exit_remaining;
	      taken_transitions = ndata.taken_transitions };
	with Not_found ->
	  begin
	    let mapped_exits = List.map (fun (x,y) -> (x.tr_name, y)) exits in
	    let nd =
	      { state = new_env;
		seen = 1;
		exit_number = List.length exits;
		exit_transitions = mapped_exits;
		exit_remaining = mapped_exits;
		taken_transitions = ExitMap.empty; } in
	    Hashtbl.add bfs_visited hash nd;
	    incr new_seen;
	    let e_m = env_to_satom_map new_env in
	    visited_states := e_m::!visited_states;
	    incr visit_count;
	    if (List.length exits) > 1 && (!steps < max_depth - 2) then
	      begin
		let f = fresh () in
		old_code := f; 
		Hashtbl.add remaining_pool f nd;
		old_pool := !pool_size; 
		incr pool_size;
		incr add_pool;
		
	      end	
	  end 
      end ;
      old_hash := hash;
      running_env := new_env;
      incr steps;
      transitions := Array.of_list (exits);
    with
      | TopError Deadlock -> Format.printf "Deadlock reached."; steps := max_depth
      | Stdlib.Sys.Break | Exit ->  steps := max_depth; raise Exit
  done;
  Format.printf "New states seen: %d. New added to pool: %d Removed from pool %d@." !new_seen !add_pool !rem_pool
    

let do_new_exit code node all_procs trans unsafes =
  let env = node.state in
  let hash = hash_full_env env in
  let removed = ref 0 in
  let added = ref 0 in
  
  try
    if (!visit_count) > Options.fuzz_s then
      begin
	Format.printf "\n\nSet limit reached@."; raise Exit
      end;

    let ee = Hashtbl.find bfs_visited hash in
    let (apply,apply_procs),lr =
      try List.hd ee.exit_remaining, List.tl ee.exit_remaining
      with Failure _ ->
	begin
	  Hashtbl.remove remaining_pool code;
	  decr pool_size;
	  Format.printf "Removed state from pool.@.";
	  raise StopExit
	end 
    in

    if lr = [] then
      begin
	Hashtbl.remove remaining_pool code;
	removed := 1;
	decr pool_size
      end
    else
      begin
	let new_map =
	  try
	    ExitMap.find (apply, apply_procs) node.taken_transitions
	  with
	      Not_found -> 0 
	in
	let ns = { state = env;
	    seen = node.seen;
	    exit_number = node.exit_number;
	    exit_transitions = node.exit_transitions;
	    exit_remaining = lr;
	    taken_transitions = ExitMap.add (apply, apply_procs) (new_map+1) node.taken_transitions; }
	in 
	Hashtbl.replace bfs_visited hash ns;
      end ;
    let new_env = apply_transition apply_procs apply trans env in
    let new_hash = hash_full_env new_env in 
    try
      let s = Hashtbl.find bfs_visited new_hash in
      let sn = 
	{ state = s.state;
	  seen = s.seen + 1;
	  exit_number =  s.exit_number;
	  exit_transitions = s.exit_transitions;
	  exit_remaining = s.exit_remaining;
	  taken_transitions = s.taken_transitions } 
      in Hashtbl.replace bfs_visited new_hash sn;
    with Not_found ->
      begin
	added := 1;
	let exits = all_possible_transitions new_env trans all_procs true in
	let mapped_exits = List.map (fun (x,y) -> (x.tr_name, y)) exits in
	let nd =
	  { state = new_env;
	    seen = 1;
	    exit_number = List.length exits;
	    exit_transitions = mapped_exits;
	    exit_remaining = mapped_exits;
	    taken_transitions = ExitMap.empty; }
	in
	Hashtbl.add bfs_visited new_hash nd;
	let e_m = env_to_satom_map new_env in
	visited_states := e_m::!visited_states;
	incr visit_count;
	let f = fresh () in
	Hashtbl.add remaining_pool f nd;
	incr pool_size
      end;
      Format.printf "Unused Exit: Added %d state(s). Removed %d state(s) from pool@." !added !removed
  with
    | StopExit -> () 
    | Exit -> raise Exit 
      

let choose_random_proc arr n =
  let r = Random.int n in
  arr.(r)      
  
let recalibrate_states () =
  Format.printf "Recalibrating remaining states...@.";
  let h' = Hashtbl.copy remaining_pool in
  let c = ref 0 in
  Hashtbl.clear remaining_pool;
  Hashtbl.iter (fun k el -> Hashtbl.add remaining_pool !c el; incr c) h'  
    
let choose_node rand =
  try
    Hashtbl.find remaining_pool rand
  with Not_found ->
    begin
      recalibrate_states ();
      Hashtbl.find remaining_pool rand
    end 

let continue_from_bfs all_procs transitions all_unsafes =
  let num_procs = Options.get_int_brab () in
  let procs = Variable.give_procs num_procs in
  let arr_procs = Array.of_list procs in
   
  Format.printf "Current number of states: %d@." !visit_count(*(List.length !visited_states)*);
  try 
  let running = ref true in
  while !running do
    if !visit_count > Options.fuzz_s then
      begin
	Format.printf "\n\nSet limit reached@."; raise Exit
      end;

    if !pool_size = 0 then begin Format.printf "No more states to explore@."; raise Exit end;
    let rand = Random.int !pool_size in
    let node = choose_node rand in
    (*choose one of four methods to explore further*)
    (* 
       - run random for X steps starting from node
       - run Markov [i.e maximizing entropy] for X steps starting from node
       - run BFS for X steps starting from node       
       - run smart for X steps starting from node
       - recalibrate remaining_pool occasionally 
    *)
    let choice = Random.int 8 in
    match choice with
      | 0 -> run_forward rand node all_procs transitions all_unsafes
      | 5 -> run_forward rand node all_procs transitions all_unsafes 
      | 1 -> markov_entropy rand node all_procs transitions
      | 2 -> recalibrate_states ()
      | 3 -> further_bfs rand node transitions all_procs all_unsafes
      | 4 -> run_smart rand node all_procs transitions all_unsafes
      | 6 -> do_new_exit rand node all_procs transitions all_unsafes
      | 7 -> force_procs_forward rand node transitions all_procs (choose_random_proc arr_procs num_procs) all_unsafes 
      | _ -> assert false   
  done
  with
    | Exit -> ()
  
    

let go_from_bfs original_env transitions all_procs all_unsafes tsys =
  List.iter (fun x -> Hashtbl.add initial_tr_count x.tr_name 0) tsys;
  interpret_bfs original_env transitions all_procs all_unsafes;
  (*if BFS finished to_do queue, there's no need to keep exploring down*)
  if !pool_size = 0 then ()
  else continue_from_bfs all_procs transitions all_unsafes 
      

let semaphore_init s =
  match s with
    | Const i -> let x = int_of_consts i in VSemaphore x
    | Elem(_, SystemProcs) -> VSemaphore !sys_procs
    | Arith _ -> VArith s
    | _ -> assert false
			

      
let init_vals env init =
  if Options.debug_interpreter then Format.eprintf "Init_vals:@.";
  (*let procs = Variable.give_procs (Options.get_interpret_procs ()) in*)
  let procs = Variable.give_procs (Options.get_int_brab ()) in
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
		  Hstring.make ("#" ^ string_of_int((Options.get_int_brab ()) + 1))
		in
		Env.add t1 (Elem(temp, Var)) sacc
	      | Elem (_, Var), Elem(_,Glob) ->
		let temp =
		  Hstring.make ("#" ^ string_of_int((Options.get_int_brab ()) + 1))
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





let print_fuzz fmt =
  Format.printf "@{<b>@{<u>@{<fg_magenta_b>Cubicle Fuzzer:@}@}@}@."
                 

let fuzz original_env transitions procs all_unsafes t_transitions =
  let s1 = String.make Pretty.vt_width '*' in
  let s2 = String.make ((Pretty.vt_width-14)/2) ' ' in
  ignore (Sys.command "clear");
  Format.printf "@{<b>@{<fg_cyan>%s@}@}" s1;
  Format.printf "%sCubicle Fuzzer%s@." s2 s2;
  Format.printf "@{<b>@{<fg_cyan>%s@}@}@." s1;
  go_from_bfs original_env transitions procs all_unsafes t_transitions;
  assert false

let brab original_env t_transitions transitions procs unsafe all_unsafes =
   go_from_bfs original_env transitions procs all_unsafes t_transitions;
  (*Format.eprintf "----------------Transitions----------------@.";
  Hashtbl.iter (fun key el -> Format.eprintf "%a ---- %d@." Hstring.print key el) fuzz_tr_count;
  Format.eprintf "-------------------------------------------@.";*)
  Format.eprintf "VISITED STATES : %d @."  !visit_count
    
  
let throwaway = Elem(Hstring.make "UNDEF", Glob)


let init tsys =
  Random.self_init ();
  let fmt = Format.std_formatter in
  let num_procs = Options.get_int_brab () in
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
  sys_procs := Options.get_int_brab ();
  let un = List.map (fun x -> 0, Node.variables x, Node.litterals x ) tsys.t_unsafe in
  let all_unsafes = init_unsafe procs un in

 (* List.iter (fun x -> Format.eprintf "unsafe: %a@." SAtom.print x) all_unsafes;*)
  
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
	  (*begin
	    match k with 
	      | Elem(n,_) | Access(n,_) -> 
		let _, ty = Smt.Symbol.type_of n in
		(Env.add k {value = random_value ty; typ = ty } env_acc, v_acc)
		(*(env_acc, v_acc)*)
	  |  _ -> assert false	
	    end*)
	  env_acc, v_acc
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
  List.iter (fun x -> Hashtbl.add fuzz_tr_count x.tr_name 0 )t_transitions;
  let original_env = env_final, lock_queue, cond_sets, semaphores in 
  let unsafe = List.map (fun x -> 0,x.cube.vars ,x.cube.litterals) tsys.t_unsafe in
  let unsafe = init_unsafe procs unsafe in
  install_sigint ();
  if Options.fuzz then
    begin
      fuzz original_env transitions procs all_unsafes t_transitions
    end 
  else
    brab original_env t_transitions transitions procs unsafe all_unsafes
 

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
  let num_procs = Options.get_int_brab () in
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
  let num_procs = Options.get_int_brab () in
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
  let num_procs = Options.get_int_brab () in
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

