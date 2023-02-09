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
	| Comp (t1, Neq, t2) -> assert false
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

let execute_random3 fmt glob_env trans all_procs unsafe applied_trans  main_bt_env tr_table steps  =  
  let hcount = Hashtbl.create 2 in 
  let backtrack_env = ref main_bt_env in
  let steps = ref steps in
  let dfile = Filename.basename Options.file in
  let open_file = open_out (dfile^".txt") in
  (*print_header open_file dfile;*)
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
      let hash = hash_full_env new_env in
      dump_hashes open_file hash;
      try
	let he = Hashtbl.find hcount hash in
	Hashtbl.replace hcount hash (he+1)
      with Not_found -> Hashtbl.add hcount hash 1;
      
      (*print_interpret_env_file open_file !running_env apply.tr_name apply_procs;*)
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
      | Stdlib.Sys.Break -> (*close_out open_file;*) running := false; Format.printf "@."
      | TopError StopExecution ->

	close_out open_file; 
	running := false
      | s ->  close_out open_file;
	let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
	assert false
  done;
  close_out open_file;
  !queue, !running_env, !backtrack_env, hcount


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
	raise (TopError Deadlock) 
      | TopError Unsafe ->
	Format.fprintf fmt
	  "Unsafe state reached after %d runs@." count;
	print_applied_trans fmt !queue;
	raise (TopError Unsafe)	
      | Stdlib.Sys.Break -> (*close_out open_file;*) running := false; Format.printf "@."
      | TopError StopExecution ->
	running := false;
	raise (TopError StopExecution)
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
      | [],[] ->
	Format.printf "└─> No parameterized transitions for %a possible\n\
                       └─> No non-parameterized transitions for %a possible\n\
                       └─> Moving on to next process@." Hstring.print proc Hstring.print proc;
	None::acc,env
      | l, [] ->
	Format.eprintf "└─> No paramaterized transitions for %a possible\n\
                        └─> Picking non-parameterized transition@." Hstring.print proc;
	let la = Array.of_list l in
	let rand = Random.int (List.length l) in
	let app,app_p = la.(rand) in
	Format.eprintf " └──> Chose transition %a@." Hstring.print app.tr_name;
	let new_env = apply_transition app_p app.tr_name trans env
	in
	check_unsafe new_env unsafe;
	Some(app,app_p)::acc, new_env                    
      | [], l ->
	Format.eprintf "└─> Only parameterized transitions for %a possible\n\
                        └─> Choosing random transition @." Hstring.print proc;
	let la = Array.of_list l in
	let rand = Random.int (List.length l) in
	let app,app_p = la.(rand) in
	Format.eprintf " └──> Chose transition %a@." Hstring.print app.tr_name;
	let new_env = apply_transition app_p app.tr_name trans env
	  
	in
	check_unsafe new_env unsafe;

	Some(app,app_p)::acc, new_env 
      | l1, l ->
	Format.eprintf "└─> Parameterized and non-parameterized transitions for %a possible\n\
                        └─> Choosing random parametrized transition @." Hstring.print proc;
	let la = Array.of_list l in
	let rand = Random.int (List.length l) in
	let app,app_p = la.(rand) in
	Format.eprintf " └──> Chose transition %a@." Hstring.print app.tr_name;
	let new_env = apply_transition app_p app.tr_name trans env
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
	      Format.eprintf "ty: %a@." Hstring.print ty;
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

  (*Format.printf "TODO--some kind of intro message and something about setting flag @.";*)
  
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
	    Hashtbl.fold (fun k el (ak, ael,overall) ->
	    Format.printf "State: %d seen %d time(s)@." k el;
	      if el > ael then (k,el,overall+el) else (ak,ael,overall+el)) hh (0,0,0) in
	  
	  Format.printf "Total entries: %d\n\
                         Total visited: %d\n\
                         State seen most often: %d [%d time(s)] @." (Hashtbl.stats hh).num_bindings overall smost smtime
	(*print_applied_trans fmt ap*)
	| TopExecRetry (i,d) ->
	  let rec aux count=
	    match count with
	      | 0 -> Format.printf "Could not detect unsafe in %d runs. Stopping.@." i
	      | _ ->
		begin 
		    try 
		      execute_depth fmt !global_env transitions procs all_unsafes !applied_trans d (i-count)
		    with
		      | TopError Deadlock ->
			Format.printf "Deadlock reached. Restarting...@.";
			aux (count - 1 )
		      | TopError StopExecution ->
			Format.printf "Depth reached. Restarting...@.";
			aux (count - 1 )
		      | TopError Unsafe ->
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
		      | TopError Deadlock ->
			Format.printf "Deadlock reached. Restarting...@.";
			aux (count - 1 ) times
		      | TopError StopExecution ->
			Format.printf "Depth reached. Restarting...@.";
			aux (count - 1 ) times 
		      | TopError Unsafe ->
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
	   
	| TopDump ->
	  (*let eee,ll,cc,semm = !global_env in
	  Format.printf "Env: %d@." (hash_env eee);
	  Format.printf "Locks: %d@." (hash_locks ll);
	  Format.printf "Cond: %d@." (hash_cond cc);
	  Format.printf "Sem: %d@." (hash_sem semm);
	    Format.printf "Full: %d@." (hash_full_env !global_env)*)
	  begin

	  let com = match Util.syscall "uname" with
	    | "Darwin\n" -> "open"
	    | "Linux\n" -> "xdg-open"
	    | _ -> (* Windows *) "cmd /c start"
	  in
	  match Sys.command ("python3 tewmp.py")
	  with
	    | 0 -> Format.eprintf "it worked??@."
	    | _ -> Format.eprintf "lol@."
	  end 
	    
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
      | s ->  let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError)
      
  done  
