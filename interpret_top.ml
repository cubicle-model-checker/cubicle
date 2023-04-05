open Ast
open Types
open Interpret_errors
open Interpret_types
open Interpret_calc
open OcamlCanvas.V1



let interpret_bool = ref true
let step_flag = ref 1
let btracks = ref []
let deadlock = ref false





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


    
let fresh = 
  let cpt = ref (-1) in
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
	| Comp (t1, Neq, t2) ->
	  begin
	    match t1, t2 with
	      | Elem(_, Glob), Elem(_, Var) ->
		let temp =
		  Hstring.make ("#" ^ string_of_int(Options.get_interpret_procs () + 1))
		in
		Env.add t1 (Elem(temp, Var)) sacc
	      | Elem (_, Var), Elem(_,Glob) ->
		let temp =
		  Hstring.make ("#" ^ string_of_int(Options.get_interpret_procs () + 1))
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
    | VInt i -> Format.fprintf fmt "\'%d\'" i
    | VReal r -> Format.fprintf fmt "\'%f\'" r
    | VBool b -> Format.fprintf fmt "\'%b\'" b
    | VConstr el | VGlob el  -> Format.fprintf fmt "\'%a\'" Hstring.print el
    | VProc i -> Format.fprintf fmt "\'%a\'" Hstring.print i
    | VLock(b, vo) ->
      if b then
	match vo with
	  | None -> assert false
	  | Some p -> Format.fprintf fmt "\'locked by process %a\'" Term.print p
      else
	Format.fprintf fmt "\'unlocked\'"
    | VAlive -> Format.fprintf fmt "\'process active\'"
    | VSuspended -> Format.fprintf fmt "\'process suspended\'"
    | VSleep _ -> Format.fprintf fmt "\'process asleep\'"
    | VRLock (b,po,i) ->
      if b then
	 match po with
	   | None -> assert false
	   | Some p -> Format.fprintf fmt "\'locked by process %a %d time(s)\'" Term.print p i
      else
	Format.fprintf fmt "\'unlocked\'"
    | VSemaphore i -> Format.fprintf fmt "\'%d\'" i
    | UNDEF -> Format.fprintf fmt "%s" "\'UNDEF\'"
    | VAccess(l,t) -> Format.fprintf fmt "\'%a[%a]\'" Hstring.print l (Hstring.print_list ", ") t
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


let dump_transitions f tr start_s go_s=
  let f = Format.formatter_of_out_channel f in
  Format.fprintf f "%d %a %d@."start_s Hstring.print tr go_s
  
let dump_hashes f hash =
  let f = Format.formatter_of_out_channel f in
  Format.fprintf f "%d@." hash


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

let execute_random3 fmt glob_env trans all_procs unsafe applied_trans main_bt_env tr_table steps  =  
  let hcount = Hashtbl.create 2 in

  let taken = ref 0 in 
  let backtrack_env = ref main_bt_env in
  let steps = ref steps in
  let dfile = Filename.basename Options.file in
  let open_file = open_out (dfile^".txt") in
  (*let old_hash = ref (hash_full_env glob_env) in*)
  (*print_header open_file dfile;*)
  Random.self_init ();
  let running_env = ref glob_env in
  let hash = hash_full_env glob_env in
  Hashtbl.replace hcount hash (1, glob_env);
  let transitions = ref (Array.of_list (all_possible_transitions glob_env trans all_procs false)) in 
  let running = ref true in
  let queue = ref applied_trans in 
  while !running (*!taken < 1500  *)do
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
      (*dump_transitions open_file apply.tr_name;*)
      let hash = hash_full_env new_env in
      (*dump_transitions open_file apply.tr_name !old_hash hash;
      old_hash := hash;*)
      (*dump_hashes open_file hash;*)
      begin
      try
	let he,ee = Hashtbl.find hcount hash in
	(*Format.eprintf "Hash: %d@." hash;
	Format.eprintf "%a@." print_interpret_env new_env;
	Format.eprintf "%a@." print_interpret_env ee;

	let hhh = hash_full_env_loud new_env in
	Format.eprintf "----------------------------@.";
	let hhhh = hash_full_env_loud ee in
	Format.eprintf "%d\n%d@." hhh hhhh;
	
	
	assert false;*)
	Hashtbl.replace hcount hash ((he+1),ee)
      with Not_found -> Hashtbl.add hcount hash (1,new_env)
      end;
      (*print_interpret_env_file open_file !running_env apply.tr_name apply_procs;*)
      if tr_num mod !step_flag = 0 then
	backtrack_env := Backtrack.add tr_num (apply.tr_name, apply_procs, new_env) !backtrack_env;
    (*;
      trace := running_env :: !trace*)
      incr taken
      
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
      | Stdlib.Sys.Break -> close_out open_file; running := false; taken := 100; Format.printf "@."
      | TopError StopExecution ->
	close_out open_file; 
	running := false
      | s ->  close_out open_file;
	let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
	assert false
  done;
  close_out open_file;
  !queue, !running_env, !backtrack_env, hcount


let find_max l =
  List.fold_left (fun (acc, mw, c) (w,tr,args) ->
    if w > mw then ([(w,tr,args)], w, 1)
    else if w = mw then ((w,tr,args)::acc, w, c+1)
    else (acc, mw, c) ) ([],-100,-100) l

let choose_random_of_equal (l, w, c) =
  if c = 0 then raise (TopError Deadlock); 
  if c = 1 then List.hd l
  else
    begin
      let l = Array.of_list l in
      Random.self_init ();
      let i = Random.int c in
      l.(i)
    end
    
    
let temp_exec glob_env trans all_procs unsafe tr depth proba systrans =
  let matrix = create_transition_hash systrans in
  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in 
  let p = if depth = 1 then true else false in
  let flag = ref false in 
  let taken = ref 0 in

  let before = Hstring.make "Init" in
  let before = ref before in 
  
  let tr = Trans.find tr trans in
  let queue = ref PersistentQueue.empty in 
  let running_env = ref glob_env in
  let transitions = ref (all_possible_weighted_transitions glob_env trans all_procs glob_env tr false)
  in
  let running = ref true in
  while !running do
    try
      let w, apply, apply_procs = choose_random_of_equal (find_max !transitions) in
      if p then
	begin
	  List.iter
	    (fun (w,t,p) -> Format.eprintf "Transition %a(%a): %d@."
	      Hstring.print t.tr_name Variable.print_vars p w) !transitions;
	  Format.eprintf "Chose: %a(%a)@." 
	    Hstring.print apply.tr_name Variable.print_vars apply_procs;
	  let _ = read_line () in ();
	end; 
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in
      let tr_num = fresh () in
      transitions := all_possible_weighted_transitions new_env trans all_procs !running_env tr !flag;
      running_env := new_env;

      let pair = (!before, apply.tr_name) in
      begin
      try
	let cpair = Hashtbl.find matrix pair in
	Hashtbl.replace matrix pair (cpair+1)
      with Not_found ->
	Hashtbl.add matrix pair 1
      end;

      before := apply.tr_name;
      
      
      queue := PersistentQueue.push (tr_num,apply.tr_name,apply_procs,-2,-2) !queue;
      incr taken;
      check_unsafe new_env unsafe;


      let hash = hash_full_env new_env in
      begin
      try
	let he,ee = Hashtbl.find hcount hash in
	Hashtbl.replace hcount hash ((he+1),ee)
      with Not_found ->
	Hashtbl.add hcount hash (1,new_env)
      end;
      let appl = procs_to_int_list apply_procs in
      List.iter (fun x ->
	proc_count.(x-1) <- proc_count.(x-1) + 1) appl;
      begin
      try
	let htc= Hashtbl.find t_count apply.tr_name in
	Hashtbl.replace t_count apply.tr_name (htc+1)
      with Not_found -> Hashtbl.add t_count apply.tr_name 1
      end ;



      

      let prob = Random.float 1.0 in
      if prob <= proba then flag := true
      else flag := false;
      (*if !taken = depth then raise (TopError StopExecution); *)
    with
      | TopError Deadlock -> running := false
      | TopError Unsafe ->
	Format.printf 
	"@{<b>@{<fg_red>WARNING@}@}: Unsafe state reached. Do you wish to continue? (y/n)@.";
	begin
	  let rec decide () =
	    let inp = read_line () in
	    match inp with
	      | "y" -> ()
	      | "n" -> running := false
	      | _ -> Format.printf  "Invalid input@."; decide ()
	  in decide ()
	end
      | Stdlib.Sys.Break -> running := false
      | Stdlib.Exit -> running := false
      | TopError StopExecution -> running := false; Format.printf "Reached max depth@."
      | s -> let s= Printexc.to_string s in Format.eprintf "%s@." s
  done;
  !queue, !running_env, (hcount,proc_count, t_count, matrix)

    
let execute_depth fmt glob_env trans all_procs unsafe applied_trans take count =
  let taken = ref 0 in 
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
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in
      running_env := new_env;
      transitions := Array.of_list (all_possible_transitions !running_env trans all_procs true);
      let lp = Array.length !transitions in
      queue := PersistentQueue.push (!taken,apply.tr_name,apply_procs, l, lp) !queue;
      incr taken;
      if take = !taken then raise (TopError StopExecution);
      check_unsafe !running_env unsafe;
    with
      | TopError Deadlock ->
	running := false;
	raise (RunError (Deadlocked(!queue,!running_env)))
      | TopError Unsafe ->
	Format.printf 
	  "Unsafe state reached after %d runs@." count;
	print_applied_trans fmt !queue;
	raise (RunError (ReachedUnsafe(!queue,!running_env)))	
      | Stdlib.Sys.Break ->running := false
      | TopError StopExecution ->
	running := false;
	raise (RunError (ReachedSteps(!queue,!running_env)))
      | Stdlib.Exit -> running := false
      | s ->  
	let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
	assert false
  done;
  raise (RunError (FinishedRun(!queue,!running_env)))
(*
depth_t : the total depth that needs to be explored
step_f : which step it crossed the transition
*)

let count_in_queue q tr =
  (*PersistentQueue.iter (fun (_,x,_,_,_) -> Format.eprintf "this is x: %a@." Hstring.print x) q;
  let d = PersistentQueue.fold (fun acc (_,x,_,_,_) ->
    if Hstring.compare tr x = 0 then (acc+1) else acc) 0 q
    in Format.eprintf "overall t3: %d@." d*)
  PersistentQueue.fold (fun acc (_,x,_,_,_) -> if Hstring.compare tr x = 0 then (acc+1) else acc) 0 q
  
let found_transition fmt original env transitions applied all_procs unsafe trace depth_t step_f tr =
  let remaining_random = (depth_t - step_f)/2 in
  let remaining_fixed = remaining_random - step_f in 
  let rec aux count q e  =
    match count with
      | 0 -> count_in_queue q tr 
      | _ ->
	begin
	  let q, e =
	try 
	   execute_depth fmt e transitions all_procs unsafe q count 0
	with
	  | RunError (ReachedUnsafe(q,e)) -> q, e
	  | RunError (Deadlocked(q,e)) -> q, e
	  | RunError (ReachedSteps(q,e)) -> q, e	    
	in
	  aux (count - 1) q e
	end 
  in
  let d1 = aux remaining_random applied original in
  let d2 = aux remaining_fixed trace env in 
  Format.eprintf "d1 is %d and d2 is %d @." d1 d2
    

let execute_depth_find_trace fmt glob_env trans all_procs unsafe applied_trans take tr =
  let steps_taken = ref 0 in
  let running_env = ref glob_env in
  let transitions =
    ref (Array.of_list (all_possible_transitions glob_env trans all_procs false))
  in
  let running = ref true in
  let queue = ref applied_trans in 
  while !running do
    try
      let l = Array.length !transitions in
      if l = 0 then raise (TopError Deadlock);
      let rand = Random.int l in
      let (apply,apply_procs) = !transitions.(rand) in
      let new_env = apply_transition apply_procs apply.tr_name trans !running_env in
      if Hstring.compare apply.tr_name tr = 0 then
	begin
	  incr steps_taken;
	  found_transition fmt glob_env !running_env trans applied_trans all_procs unsafe !queue take !steps_taken tr
	end
      else
	begin
	  running_env := new_env;
	  transitions := Array.of_list (all_possible_transitions !running_env trans all_procs true);
	  let lp = Array.length !transitions in
	  queue := PersistentQueue.push (!steps_taken,apply.tr_name,apply_procs, l, lp) !queue;
	  incr steps_taken;
	  check_unsafe !running_env unsafe 
	end

    with
      | TopError Deadlock -> assert false
	 
      | TopError Unsafe -> assert false
	
      | Stdlib.Sys.Break ->  assert false
      | TopError StopExecution -> assert false

      | s ->  (*close_out open_file;*)
	let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
	assert false
  done
 


    

    
let dump_in_file  (env,locks, cond, sem) file =
  let f = Format.formatter_of_out_channel file in
  Format.fprintf f "[\n"; 
  Env.iter( fun k {value = v } ->
    Format.fprintf f "[\'%a\'," Term.print k; print_val f v; Format.fprintf f "],\n"
  ) env;
  Format.fprintf f "];"
  

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
  

let proc_of_int proc =
  let s = string_of_int proc in
  Hstring.make ("#"^s)
(*--------------*)

  
let gen_list depth =
  assert (depth >= 0);
  Random.self_init ();
  let all = Options.get_interpret_procs () in
  let rec aux depth acc =
    match depth with
      | 0 -> acc
      | _ -> let elem = (Random.int all) + 1 in
	     aux (depth - 1) (proc_of_int elem::acc)
  in aux depth []


(*--------------*)
let hash_of_env env transitions =
  Trans.iter (fun k el ->
    Format.eprintf "k = %a and hash = %d@." Hstring.print k (Hashtbl.hash k)) transitions
(*--------------*)

  
let run_from_list env trans all_procs follow unsafe=
  List.fold_left (fun (acc,env) proc ->
    Format.printf "\n--Trying for process %a--@." Hstring.print proc;
    Random.self_init ();
    let npl, pl = possible_for_proc env trans all_procs proc in
    match npl,pl with
      | ([],[]),_ ->
	Format.printf "└─> No parameterized transitions for %a possible\n\
                       └─> No non-parameterized transitions for %a possible\n\
                       └─> Moving on to next process@." Hstring.print proc Hstring.print proc;
	None::acc,env
      | (l, []), nv ->
	Format.eprintf "└─> No paramaterized transitions for %a possible\n\
                        └─> Picking non-parameterized transition@." Hstring.print proc;
	let la = Array.of_list l in
	let rand = Random.int (List.length l) in
	let app,app_p = la.(rand) in
	Format.eprintf " └──> Chose transition %a@." Hstring.print app.tr_name;
	let _, l1,l2,l3 = env in	
	let new_env = apply_transition app_p app.tr_name trans (nv,l1,l2,l3)
	in
	check_unsafe new_env unsafe;
	Some(app,app_p)::acc, new_env                    
      | ([], l), nv ->
	Format.eprintf "└─> Only parameterized transitions for %a possible\n\
                        └─> Choosing random transition @." Hstring.print proc;
	let la = Array.of_list l in
	let rand = Random.int (List.length l) in
	let app,app_p = la.(rand) in
	Format.eprintf " └──> Chose transition %a@." Hstring.print app.tr_name;
	let _, l1,l2,l3 = env in	
	let new_env = apply_transition app_p app.tr_name trans (nv,l1,l2,l3)
	  
	in
	check_unsafe new_env unsafe;

	Some(app,app_p)::acc, new_env 
      | (l1, l), nv ->
	Format.eprintf "└─> Parameterized and non-parameterized transitions for %a possible\n\
                        └─> Choosing random parametrized transition @." Hstring.print proc;
	let la = Array.of_list l in
	let rand = Random.int (List.length l) in
	let app,app_p = la.(rand) in
	Format.eprintf " └──> Chose transition %a@." Hstring.print app.tr_name;
	let _, l1,l2,l3 = env in	
	let new_env = apply_transition app_p app.tr_name trans (nv,l1,l2,l3)
	in
	check_unsafe new_env unsafe;
	
	Some(app,app_p)::acc, new_env 
  )  ([],env) follow
  
(*--------------*)
    
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
  let all_unsafes = init_unsafe procs sys.unsafe in
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
 
  
    (*let env_final =
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
	      Format.eprintf "ty: %a@." Hstring.print ty;
	      if is_semaphore ty then
		  {value = semaphore_init x; typ = ty}
	      else
		{value = cub_to_val x ; typ = ty }
	    | _ -> assert false
	end
      ) env in*)
   let env_final =
      Env.fold (fun k x acc ->
	match x.value with
	  | VGlob n ->
	    Format.eprintf "Trying n %a@." Hstring.print n;
	    let vg = Env.find (Elem(n,Glob)) acc in
	    begin
	      match vg.value with
		| VGlob n1 ->
		  Format.eprintf "Trying n1 %a@." Hstring.print n1;
		  begin
		    let vg2 = Env.find (Elem (n1,Glob)) acc in
		    let tt = 
		      match vg2.value with
			| VGlob n2 ->
			  Format.eprintf "Trying n2 %a@." Hstring.print n2;
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
	(*| VGlob vg ->
	  let v = Env.find (Elem(vg, Glob)) env in
	  begin
	    match v.value with
	      | VGlob vg' -> 
	  end *)
	| _ ->
	  Format.eprintf "k is %a and typ is %a@." Term.print k Hstring.print x.typ;x


    ) env_final in
  
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
  
  while !interpret_bool do
    try
      flush stdout; Format.printf "> %!";
      let inp = read_line () in      
      let tts = Parser.toplevel Interpret_lexer.token (Lexing.from_string inp) in
      
      (match tts with
	| TopExec ->
	  let ap, g, be, hh  =
	    execute_random3 fmt !global_env
	      transitions procs all_unsafes !applied_trans !backtrack_env tr_table !steps 
	  in
	  global_env := g;
	  applied_trans := ap;
	  backtrack_env := be;
	  let smost,smtime,overall =
	    Hashtbl.fold (fun k (el,envoo) (ak, ael,overall) ->
	      (*Format.printf "State: %d seen %d time(s)@." k el;*)
	      (*print the state it saw multiple times*)
	      if el > 1 then Format.printf "State: %d -- %a@." k  print_interpret_env envoo;

	      if el > ael then (k,el,overall+el) else (ak,ael,overall+el)) hh (0,0,0) in

	  (*Hashtbl.iter (fun k (el,envoo) ->
	    Format.eprintf "State: %d, env: %a@." k print_interpret_env envoo) hh;*)
	  
	  Format.printf "Total entries: %d\n\
                         Total visited: %d\n\
                         State seen most often: %d [%d time(s)] @." (Hashtbl.stats hh).num_bindings overall smost smtime
	 (* Hashtbl.iter (fun k (_,el) ->
	    Format.printf "%a@." print_interpret_env el) hh*)







	    
	| TopExecRetry (i,d) ->
	  let rec aux count=
	    match count with
	      | 0 -> Format.printf "Could not detect unsafe in %d runs. Stopping.@." i
	      | _ ->
		begin 
		    try 
		      execute_depth fmt !global_env transitions procs all_unsafes !applied_trans d (i-count)
		    with
		      | RunError Deadlocked _ ->
			Format.printf "Deadlock reached. Restarting...@.";
			aux (count - 1 )
		      | RunError ReachedSteps _ ->
			Format.printf "Depth reached. Restarting...@.";
			aux (count - 1 )
		      | RunError ReachedUnsafe _->
			Format.printf "Search terminated@.";
		      | _ -> assert false
		end
	  in aux i

	| TopCount(i,d) ->
	  let rec aux count times =
	    match count with
	      | 0 -> Format.printf "\nDetected state %d time(s) out of %d runs@." times i
	      | _ ->
		begin 
		    try 
		      execute_depth fmt !global_env transitions procs all_unsafes !applied_trans d (i-count)
		    with
		      | RunError Deadlocked _ ->
			Format.printf "Deadlock reached. Restarting...@.";
			aux (count - 1 ) times
		      | RunError ReachedSteps  _ ->
			Format.printf "Depth reached. Restarting...@.";
			aux (count - 1 ) times 
		      | RunError ReachedUnsafe _  ->
			Format.printf "Unsafe reached. Restarting...@.";
			aux (count -1) (times+1)
		      | _ -> assert false
		end
	  in aux i 0
	  
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
	| TopUnsafe -> check_unsafe !global_env all_unsafes
	| TopRestart ->
	  global_env := original_env;
	  applied_trans := PersistentQueue.empty;
	  backtrack_env := Backtrack.empty;
	  Hashtbl.reset tr_table;
	  steps := 0;
	  print_interpret_env fmt !global_env
	   
	| TopGenProc -> global_env := generate_process !global_env num_procs tsys
	| TopPrintSys -> Ptree.print_system fmt sys

	| TopRandom ->
	  let ap, g, be, ste =
	    pick_random fmt !global_env
	      transitions procs all_unsafes !applied_trans [] !backtrack_env !steps tr_table
	  in
	  global_env := g;
	  applied_trans := ap;
	  backtrack_env := be;
	  steps := ste
		       

	| TopFuzz n ->
	  let l = gen_list n in
	  let _ = run_from_list !global_env transitions procs l all_unsafes in
	  ()

	| TopExperiment (t,dep,prob) ->
	  (*dep will be dep later, it is currently flag to print steps or nah*)
	  let q, e, (hh,pc,tc,matrix) = temp_exec !global_env transitions procs all_unsafes t dep prob sys.trans 
	  in
	  global_env := e;
	  applied_trans := q;


	  let smost,smtime,overall =
	    Hashtbl.fold (fun k (el,envoo) (ak, ael,overall) ->
	      if el > ael then (k,el,overall+el) else (ak,ael,overall+el)) hh (0,0,0) in
 
	  Format.printf "Total entries: %d\n\
                 Total visited: %d\n\
                 State seen most often: %d [%d time(s)] @."
	    (Hashtbl.stats hh).num_bindings overall smost smtime;
	  
	  Array.iteri (fun i a -> Format.eprintf "Proc %d : %d times@." (i+1) a) pc;
	  
	  Hashtbl.iter (fun k el -> Format.eprintf "Transition %a : %d times@." Hstring.print k el) tc;
	  
	  Hashtbl.iter (fun (k,k1) el -> Format.eprintf "(%a->%a) : %d @." Hstring.print k Hstring.print k1 el) matrix


	| TopMarkov t -> ()
	  (*let tr = Trans.find t transitions in 
	  
	    Interpret_exp.run !global_env sys.trans procs tr transitions*)



	| TopMCMC(mthd, flg, mc_steps) ->
	  Interpret_exp.run !global_env sys.trans procs transitions mthd flg mc_steps


	    
	   
	| TopDump ->

	  

	  let pp = Variable.give_procs (Options.get_interpret_procs ()) in

	  (*List.iter (fun x -> Format.eprintf "%a@." Hstring.print x) pp;*)

	  let p_m,_ = List.fold_left (fun (acc, count) x ->
	    let pl = Hstring.make("mapped_"^(string_of_int count))
	    in Format.eprintf "pm: %a --> %a@." Hstring.print x Hstring.print pl;
	     ((pl,x)::acc, count+1)
	  ) ([], 0) pp in

	  (*let susig = Variable.build_subst pp p_m in*)

	  let back_to_proc = p_m in (*Variable.build_subst p_m pp in*)

	  Format.eprintf "System Map:@.";
	  List.iter (fun (z, y) ->
	    Format.eprintf "%a -> %a @." Hstring.print z Hstring.print y) back_to_proc;


	  let el1 = Access(Hstring.make "P", [Hstring.make "#1"]) in
	  let el2 = Access(Hstring.make "P", [Hstring.make "#2"]) in

	  let eN1 = Access(Hstring.make "P", [Hstring.make "#4"]) in
	  let eN2 = Access(Hstring.make "P", [Hstring.make "#5"]) in


	  

	  
	  let el3 = Elem(Hstring.make "A", Constr) in
	  let el4 = Elem(Hstring.make "B", Constr) in
	  let el5 = Elem(Hstring.make "G", Glob) in
	  let el6 = Elem(Hstring.make "#1", Var) in

	  let s1 = Atom.Comp(el1, Eq, el3) in
	  let s2 = Atom.Comp(el2, Eq, el4) in

	  let sN1 = Atom.Comp(el1, Neq, el4) in
	  let sN2 = Atom.Comp(el2, Eq, el4) in
	  
	  let s3 = Atom.Comp(el5, Eq, el6) in

	  let sa = SAtom.add s1 SAtom.empty in
	  (*let sa = SAtom.add s2 sa in
	  let sa = SAtom.add s3 sa in*)

	  let sa2 = SAtom.add sN1 SAtom.empty in


	  Format.eprintf "??%b@." (SAtom.subset sa2 sa);
	  assert false;
	  (*let sa2 = SAtom.add sN2 sa2 in*)

	  let pl = extract_procs sa in
	  let map1 = gen_mapping pl in
	  
	  Format.eprintf "Map1:@.";
	  List.iter (fun (z, y) ->
	    Format.eprintf "%a -> %a @." Hstring.print z Hstring.print y) map1;

	  let sa_s = SAtom.subst map1 sa in

	  let pl2 = extract_procs sa2 in
	  let map2 = gen_mapping pl2 in

	  Format.eprintf "Map2:@.";
	  List.iter (fun (z, y) ->
	    Format.eprintf "%a -> %a @." Hstring.print z Hstring.print y) map2;
	  

	  let sa2_s = SAtom.subst map2 sa2 in 

	  let normalized_1 = SAtom.subst back_to_proc sa_s in
	  let normalized_2 = SAtom.subst back_to_proc sa2_s in

	  
	  Format.eprintf "Subbed: %a@." SAtom.print normalized_1;

	  Format.eprintf "Subbed2: %a@." SAtom.print normalized_2;

	  (*let subbSA = SAtom.subst susig sa in

	  Format.eprintf "Subbed: %a@." SAtom.print subbSA;

	  let u_procs = all_arrange (Options.get_interpret_procs ()) procs in

	  List.iter (fun x ->
	    let si = Variable.build_subst p_m x in 
	    Format.eprintf "Test: %a@."
	    SAtom.print (SAtom.subst si subbSA)) u_procs;*)


      

	  assert false
	  
	  (*let en_env = Enumerative.mk_env 3 tsys in
	  let tt = Elem(Hstring.make "A", Constr) in
	  let ttt = Elem(Hstring.make "X", Glob) in 
	  Format.eprintf "%d@." (Enumerative.int_of_term en_env ttt);
	  assert false*)
	   
	  
	  
	  (*execute_depth_find_trace fmt !global_env transitions procs all_unsafes !applied_trans
	    10 (Hstring.make "t3")*)




	(*Interpret_run.run !global_env transitions procs all_unsafes !applied_trans sys.trans*)



	  
	  
	  (*List.iter (fun x -> Format.eprintf "unsafe: %a@." SAtom.print x) all_unsafes*)
	  (*let _ = 
	  execute_depth_find_trace fmt !global_env transitions procs all_unsafes !applied_trans 10 (Hstring.make "t2") in ()*)
	  (*let eee,ll,cc,semm = !global_env in
	  Format.printf "Env: %d@." (hash_env eee);
	  Format.printf "Locks: %d@." (hash_locks ll);
	  Format.printf "Cond: %d@." (hash_cond cc);
	  Format.printf "Sem: %d@." (hash_sem semm);
	    Format.printf "Full: %d@." (hash_full_env !global_env)*)
	  
	(*begin

	  let _com = match Util.syscall "uname" with
	    | "Darwin\n" -> "open"
	    | "Linux\n" -> "xdg-open"
	    | _ -> (* Windows *) "cmd /c start"
	  in
	  match Sys.command("python3 temp.py") 
	  with
	    | 0 ->  Format.eprintf "--python done@."
	    | _ -> Format.eprintf "Error with python@."
	  end *)
	    
	  (*hash_of_env !global_env transitions*)
	  
	  (*let dfile = Filename.basename Options.file in
	  let open_file = open_out (dfile^".txt") in
	  dump_in_file !global_env open_file;
	    close_out open_file*)
	  (*let p1 = Hstring.make "#1" in
	  let l = possible_for_proc !global_env transitions procs p1 in
	  print_poss_trans fmt l;
	  Format.eprintf "list %d@." (List.length l);*)
	  
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
      (*| s ->  let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError)
      *)
  done  
