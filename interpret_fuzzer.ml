open Interpret_calc
open Interpret_types
open Interpret_errors
open Ast
open Types
open Util


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

let unsafe_states = ref []
let dead_states = ref []

let parents = Hashtbl.create 200


  
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


let print_interpret_env fmt (env,locks, cond, sem)=
  Env.iter(fun k {value = v} ->
    Format.fprintf fmt "%a : %a\n" Term.print k print_val v
  ) env;
  Format.fprintf fmt "----------------------\n";
  Format.fprintf fmt "Lock Queues:\n";
  LockQueues.iter (fun k el ->
    Format.fprintf fmt "%a : { %a }\n" Term.print k print_queue el) locks;
  Format.fprintf  fmt "----------------------\n";
    Format.fprintf fmt "Condition wait pools:\n";
  Conditions.iter (fun k el ->
    Format.fprintf fmt "%a : { %a }\n" Term.print k print_wait el) cond;
  Format.fprintf fmt "----------------------\n";
  Format.fprintf fmt "Semaphore wait lists:\n";
  Semaphores.iter (fun k el ->
    Format.fprintf fmt "%a : { %a }\n" Term.print k print_wait el) sem

    

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


exception ReachedUnsafe
exception NeverSeen of Interpret_types.global * (Ast.transition_info * Variable.t list) * int
exception StopExit
exception Dead of int
exception Done
  

let reconstruct_trace parents me =
  let trace = ref [] in
  let bad = ref me in
  let not_init = ref true in
  while !not_init do
    let am_init, tr, h= Hashtbl.find parents !bad in
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


let reconstruct_trace_file fmt parents me =
  let trace = ref [] in
  let bad = ref me in
  let init_hash = ref 0 in
  let not_init = ref true in
  while !not_init do
    let am_init, tr, h= Hashtbl.find parents !bad in
    if am_init then
      begin
	not_init := false;
	init_hash := h
      end 
    else
      begin
	match tr with
	  | Some (t,tr_pr) -> trace := (t.tr_name,tr_pr, h)::!trace; bad := h
	  | None -> assert false
      end
  done;
  Format.fprintf fmt "Trace:\n";
  Format.fprintf fmt "Init[%d]" !init_hash;
  List.iter (fun (x,y,hsh) -> Format.fprintf fmt " -> %a(%a)[%d]" Hstring.print x Variable.print_vars y hsh)  !trace;
  Format.fprintf fmt "\n"
    
  

let least_taken_exit s =
  let exits = s.taken_transitions in
  let first = ExitMap.choose exits in 
  ExitMap.fold (fun key el (k,acc) ->
    if el < acc then (key,el) else (k,acc)) exits first




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
	    let new_map =
	      try
		ExitMap.find (apply.tr_name, apply_procs) data.taken_transitions
	      with
		  Not_found -> 0 
	    in
	    Hashtbl.replace initial_data !old_hash
	      { state = data.state;
		seen = data.seen + 1;
		exit_number = data.exit_number;
		exit_transitions = data.exit_transitions;
		exit_remaining = List.filter (fun x ->
		  not (compare_exits x (apply.tr_name, apply_procs))
		) data.exit_remaining;
		taken_transitions =
		  ExitMap.add (apply.tr_name, apply_procs) (new_map+1) data.taken_transitions;
		
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

	  incr visit_count;
	  let mapped_exits = List.map (fun (x,y) -> (x.tr_name, y)) exits in
	  Hashtbl.add initial_data hash
	    { state = new_env;
	      seen = 0 ;
	      exit_number = List.length exits;
	      exit_transitions = mapped_exits;
	      exit_remaining = mapped_exits;
	      taken_transitions = ExitMap.empty;
	      
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
      transitions := exits;
      (*count seen states*)
      
    with
      | TopError Deadlock ->
	let dead_hash = hash_full_env !running_env in
	Hashtbl.add deadlock_states dead_hash { dead_state = !running_env;
						dead_path = !queue;
						dead_steps = !steps;
						dead_predecessor = !old_env} ;
	begin
	  try
	    let dh = Hashtbl.find dead_preds !old_hash in
	    Hashtbl.add dead_preds !old_hash (dead_hash::dh)
	  with Not_found -> 
	    Hashtbl.add dead_preds !old_hash [dead_hash] ;
	end;
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

    
let markov_entropy code glob all_procs trans all_unsafes=
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
		incr visit_count;
		Hashtbl.add parents hash (false, Some (proposal, prop_procs), !old_hash);
		begin
		  try
		    check_unsafe temp_env all_unsafes;
		  with
		| TopError Unsafe ->
		  Format.printf "\n@{<b>@{<bg_red>WARNING@}@}@.";
		  unsafe_states := hash :: !unsafe_states;
		  Format.printf "@{<fg_red>Unsafe state reached during forward exploration@}@.";
		  (*reconstruct_trace parents hash;
		  raise ReachedUnsafe*)
		end;
		incr new_seen;
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
	taken := steps;
	
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
    

let run_smart code node all_procs trans all_unsafes =
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
	    incr visit_count;
	    Hashtbl.add parents hash (false, Some (apply, apply_procs), !old_hash);
	    begin
	      try
		check_unsafe temp_env all_unsafes;
	      with
		| TopError Unsafe ->
		  Format.printf "\n@{<b>@{<bg_red>WARNING@}@}@.";
		  Format.printf "@{<fg_red>Unsafe state reached during forward exploration@}@.";
		  unsafe_states := hash :: !unsafe_states
	    (*reconstruct_trace parents hash;
	      raise ReachedUnsafe*)
	    end;
	    incr new_seen;
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
    let max_depth = Random.int 10 in
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
      let ha, env_d, env = Queue.pop to_do in
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
	    incr visit_count;
	    Hashtbl.add parents he (false, Some (at, at_p), ha);
	    begin
	      try
		check_unsafe e all_unsafes;
	      with
		| TopError Unsafe ->
		  Format.printf "\n@{<b>@{<bg_red>WARNING@}@}@.";
		  Format.printf "@{<fg_red>Unsafe state reached during forward exploration@}@.";
		  unsafe_states := he :: !unsafe_states
		  (*reconstruct_trace parents he;
		  raise ReachedUnsafe*)
	    end;
	    incr new_seen;

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
    let max_depth = 5 in
    let curr_depth = ref 0 in
    let node = ref 0 in
    let rem = ref 1 in
    let time_limit = 10.0 in
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
    incr visit_count;
    let to_do = Queue.create () in
    Queue.push (he, 0,original_env) to_do;
    Hashtbl.add parents he (true, None, he);
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
	    incr visit_count;
	    Hashtbl.add parents he (false, Some (at, at_p), ha);
	    begin
	      try
		check_unsafe e all_unsafes;
	      with
		| TopError Unsafe ->
		  Format.printf "\n@{<b>@{<bg_red>WARNING@}@}@.";
		  Format.printf "@{<fg_red>Unsafe state reached during forward exploration@}@.";
		  unsafe_states := he :: !unsafe_states
		  (*reconstruct_trace parents he;
		  raise ReachedUnsafe*)
	    end;
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
      
      



let run_forward code node all_procs trans all_unsafes =
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
	    incr visit_count;
	    Hashtbl.add parents hash (false, Some (apply, apply_procs), !old_hash);
	    begin
	      try
		check_unsafe new_env all_unsafes;
	      with
		| TopError Unsafe ->
		  Format.printf "\n@{<b>@{<bg_red>WARNING@}@}@.";
		  Format.printf "@{<fg_red>Unsafe state reached during forward exploration@}@.";
		  unsafe_states := hash :: !unsafe_states;
		  (*reconstruct_trace parents hash;
		  raise ReachedUnsafe*)
	    end;
	    incr new_seen;
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
    

let do_new_exit code node all_procs trans all_unsafes =
  let env = node.state in
  let hash = hash_full_env env in
  let removed = ref 0 in
  let added = ref 0 in
  
  try
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
    let tr = Trans.find apply trans in 
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
	incr visit_count;
	Hashtbl.add parents new_hash (false, Some (tr, apply_procs), hash);
	begin
	  try
	    check_unsafe new_env all_unsafes;
	  with
	    | TopError Unsafe ->
	      Format.printf "\n@{<b>@{<bg_red>WARNING@}@}@.";
	      Format.printf "@{<fg_red>Unsafe state reached during forward exploration@}@.";
	      unsafe_states := new_hash :: !unsafe_states;
	      (*reconstruct_trace parents new_hash;
	      raise ReachedUnsafe*)
	end;

	let f = fresh () in
	Hashtbl.add remaining_pool f nd;
	incr pool_size
      end;
      Format.printf "Unused Exit: Added %d state(s). Removed %d state(s) from pool@." !added !removed
  with
    | StopExit -> () 
    | Exit -> raise Exit 
    
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
  Format.printf "Current number of states: %d@." (List.length !visited_states);
  try 
  let running = ref true in
  while !running do
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
    let choice = Random.int 7 in
    match choice with
      | 0 -> run_forward rand node all_procs transitions all_unsafes
      | 5 -> run_forward rand node all_procs transitions all_unsafes 
      | 1 -> markov_entropy rand node all_procs transitions all_unsafes
      | 2 -> recalibrate_states ()
      | 3 -> further_bfs rand node transitions all_procs all_unsafes
      | 4 -> run_smart rand node all_procs transitions all_unsafes
      | 6 -> do_new_exit rand node all_procs transitions all_unsafes 
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




module TimerFuzz = Timer.Make (struct let profiling = true end)


let print_fuzz fmt =
  Format.printf "@{<b>@{<u>@{<fg_magenta_b>Cubicle Fuzzer:@}@}@}@."


let print_time fmt sec =
  let minu = floor (sec /. 60.) in
  let extrasec = sec -. (minu *. 60.) in
  Format.printf  "%dm%2.3fs" (int_of_float minu) extrasec
    

let print_time fmt sec =
  let minu = floor (sec /. 60.) in
  let extrasec = sec -. (minu *. 60.) in
  Format.fprintf fmt "%dm%2.3fs" (int_of_float minu) extrasec

let print_transitions fmt () = 
  Format.fprintf fmt "----------------Transitions----------------\n";
  Hashtbl.iter (fun key el -> Format.fprintf fmt "%a:%d\n" Hstring.print key el) fuzz_tr_count;
  Format.fprintf fmt "-------------------------------------------\n"


let print_unsafes fmt () =
  Format.fprintf fmt "Unsafe states:\n";
  List.iter (fun un ->
    reconstruct_trace_file fmt parents un ) !unsafe_states

let print_deadlocks fmt () =
  Format.fprintf fmt "Deadlock states:\n";
  List.iter (fun dead ->
    reconstruct_trace_file fmt parents dead ) !dead_states    

    
let write_file name fn = 
  let f = Format.formatter_of_out_channel fn in
  Format.fprintf f "File: %s\n\
                  Time elapsed: %a\n\
                  Procs: %d\n\
                  Visited states: %d\n\
                  Remaining pool: %d\n\
                  %a\n\
                  %a\n\
                  %a@."
    name
    print_time (TimerFuzz.get ())
    (Options.get_interpret_procs ())
    !visit_count
    !pool_size
    print_transitions ()
    print_unsafes ()
    print_deadlocks ()

let write_states_to_file name =
  let open_file = open_out (name^".states") in
  let f = Format.formatter_of_out_channel open_file in
  Hashtbl.iter (fun key el ->
    Format.fprintf f "[%d]\n\
                      %a@."
      key
      print_interpret_env el.state ) bfs_visited;
  close_out open_file 
  
    


        
let fuzz original_env transitions procs all_unsafes t_transitions =
  TimerFuzz.start ();
  let s1 = String.make Pretty.vt_width '*' in
  let s2 = String.make ((Pretty.vt_width-14)/2) ' ' in
  ignore (Sys.command "clear");
  Format.printf "@{<b>@{<fg_cyan>%s@}@}" s1;
  Format.printf "%sCubicle Fuzzer%s@." s2 s2;
  Format.printf "@{<b>@{<fg_cyan>%s@}@}@." s1;

  let dfile = Filename.basename Options.file in
  let open_file = open_out (dfile^".stats") in
  
  go_from_bfs original_env transitions procs all_unsafes t_transitions;
  TimerFuzz.pause ();
  Format.printf "├─Time elapsed       : %a@." print_time (TimerFuzz.get ());
  write_file dfile open_file;
  close_out open_file;
  write_states_to_file dfile;
  raise Done
  

let throwaway = Elem(Hstring.make "UNDEF", Glob)


let init tsys =
  Random.self_init ();
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
  fuzz original_env transitions procs all_unsafes t_transitions
    
