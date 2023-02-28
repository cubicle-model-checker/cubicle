open Interpret_types
open Interpret_calc
open Interpret_errors
open Ast
open Types


let fresh_back = 
  let cpt = ref 0 in
  fun () -> incr cpt; !cpt



let all_combs_as_pairs l =
  let rec combs l acc = 
    match l with 
      | [] -> acc 
      | [hd] -> (hd,hd)::acc
      | hd::tl -> let a = 
		    List.fold_left
		      (fun acc1 el -> (hd,el)::(el,hd)::acc1) ((hd,hd)::acc) tl
		  in combs tl a
  in combs l []

      
let create_transition_hash t =
  let stemp = (float (List.length t))** 2. in
  let size = int_of_float stemp in

  let ht = Hashtbl.create size in
  let names = List.map (fun x -> x.tr_name) t in
  let names = (Hstring.make "Init") :: names in
  let all_combs = all_combs_as_pairs names in
  List.iter (fun x -> Hashtbl.add ht x 0) all_combs;
  
  ht

    

let execute_random3 glob_env trans all_procs unsafe applied_trans systrans=
  let matrix = create_transition_hash systrans in

  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in 
  let steps = ref 0 in
  Random.self_init ();
  let running_env = ref glob_env in
  let transitions = ref (Array.of_list (all_possible_transitions glob_env trans all_procs false)) in 
  let running = ref true in

  let before = Hstring.make "Init" in
  let before = ref before in 
  
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
      queue := PersistentQueue.push (tr_num, apply.tr_name,apply_procs, l, lp) !queue;
      check_unsafe !running_env unsafe;


      let pair = (!before, apply.tr_name) in
      begin
      try
	let cpair = Hashtbl.find matrix pair in
	Hashtbl.replace matrix pair (cpair+1)
      with Not_found ->
	Hashtbl.add matrix pair 1
      end;

      before := apply.tr_name;
     

      
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
     
    with
      | TopError Deadlock ->
	Format.printf 
	  "@{<b>@{<fg_red>WARNING@}@}: Deadlock reached@."; running := false;
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
      | Stdlib.Sys.Break ->  running := false; Format.printf "@."
      | TopError StopExecution ->
	running := false
      | s -> 
	let e = Printexc.to_string s in Format.printf "%s %a@." e top_report (InputError);
	assert false
  done;
  !queue, !running_env, (hcount,proc_count, t_count,matrix)


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

let fresh_tr = 
  let cpt = ref (-1) in
  fun () -> incr cpt; !cpt

let rec find_tr array name procs c =
  let (n,p),i = array.(c) in
  if Hstring.equal n.tr_name name && (Hstring.compare_list procs p = 0) then i  
  else find_tr array name procs (c+1)
  

    
let wl glob_env trans all_procs tsys steps =
  Random.self_init ();

  
  let matrix = create_transition_hash tsys in
  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in

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
  let tr_array = Array.map (fun x -> (x,fresh_tr ())) tr_array in

  let hist = Array.make els 0. in
  let lng = Array.make els 0. in

  let flatness = 0.8 in
  let f = ref 1.0 in

  let epsilon = 0.0000001 in 


  let taken = ref 0 in

  let tn,tp = List.hd (all_possible_transitions glob_env trans all_procs false)
  in
  let n = apply_transition tp tn.tr_name trans glob_env in
  let ii = find_tr tr_array tn.tr_name tp 0 in

  let pair = Hstring.make "Init", tn.tr_name in
  Hashtbl.replace matrix pair 1;

  let appl = procs_to_int_list tp  in
  List.iter (fun x ->
    proc_count.(x-1) <- proc_count.(x-1) + 1) appl;

  let hash = hash_full_env n in
  Hashtbl.replace hcount hash (1,n);
  Hashtbl.replace t_count tn.tr_name 1;
  

  let running_env = ref n in

  let old_index = ref ii in

  let before = ref tn.tr_name in
  let before_procs = ref tp in 



  while !taken < steps do
    try 

    let env, _,_,_ = !running_env in 
    let rand = Random.int els in
    let (proposal,prop_procs),index = tr_array.(rand) in


    let sigma = Variable.build_subst proposal.tr_args prop_procs in
      
      (*check_actor_suspension sigma !global_env proposal.tr_process;*)
      
      check_reqs proposal.tr_reqs env sigma proposal.tr_name;
      let trargs = List.map (fun x -> Variable.subst sigma x) proposal.tr_args in
      let ureqs = uguard !running_env sigma all_procs trargs proposal.tr_ureq in
      List.iter (fun u -> check_reqs u env sigma proposal.tr_name) ureqs;

      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in

      let p = 2.718281828** (lng.(!old_index) -. lng.(index)) in
      let rand = Random.float 1. in

      if p > rand then
	begin
	  old_index := index; 
	  running_env := temp_env;
	  hist.(index) <- hist.(index)+. 1.;
	  lng.(index) <- lng.(index) +. !f;

	  let pair = (!before, proposal.tr_name) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found ->
	      Hashtbl.add matrix pair 1
	  end;
	  
	  before := proposal.tr_name;
	  before_procs := prop_procs; 
	  
	  let hash = hash_full_env temp_env in
	  begin
	    try
	      let he,ee = Hashtbl.find hcount hash in
	      Hashtbl.replace hcount hash ((he+1),ee)
	    with Not_found ->
	      Hashtbl.add hcount hash (1,temp_env)
	  end;
	  let appl = procs_to_int_list prop_procs in
	  List.iter (fun x ->
	    proc_count.(x-1) <- proc_count.(x-1) + 1) appl;
	  begin
	    try
	      let htc= Hashtbl.find t_count proposal.tr_name in
	      Hashtbl.replace t_count proposal.tr_name (htc+1)
	    with Not_found -> Hashtbl.add t_count proposal.tr_name 1
	  end ;
	  
	end
      else
	begin
	  hist.(!old_index) <- hist.(!old_index)+. 1.;
	  lng.(!old_index) <- lng.(!old_index) +. !f;


	  let pair = (!before, !before) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found ->
	      Hashtbl.add matrix pair 1
	  end;
	  	  
	  let hash = hash_full_env !running_env in
	  begin
	    try
	      let he,ee = Hashtbl.find hcount hash in
	      Hashtbl.replace hcount hash ((he+1),ee)
	    with Not_found ->
	      Hashtbl.add hcount hash (1,!running_env)
	  end;
	  (*let appl = procs_to_int_list !before_procs in
	  List.iter (fun x ->
	    proc_count.(x-1) <- proc_count.(x-1) + 1) appl;
	  begin
	    try
	      let htc= Hashtbl.find t_count !before in
	      Hashtbl.replace t_count !before (htc+1)
	    with Not_found -> Hashtbl.add t_count proposal.tr_name 1
	  end ;*)



	  
	end;

      if !taken mod 100 = 0 then
	begin
	  let sum = Array.fold_left (fun acc el -> el+. acc) 0. hist in 
	  let aH = sum /. (float els) in
	  let mH = Array.fold_left (fun el acc -> if el < acc then el else acc) hist.(0) hist in
	  if mH > (aH *. flatness) then
	    begin
	      Array.iteri (fun i el -> hist.(i) <- 0.) hist;
	      f := !f /.2.
	    end
	end;
      incr taken
    with
      | TopError Deadlock -> taken := steps
      | TopError (FalseReq _) -> ()
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> taken := steps
 
  done ;
  !running_env, (hcount,proc_count, t_count,matrix), hist, lng, tr_array 
  

  


    


let run glob_env trans all_procs unsafe applied_trans systrans=
  
  let (*q,*) e, (hh,pc,tc,matrix), hist, lng, tr_array =
    wl glob_env trans all_procs systrans 1000000 in
  (*execute_random3 glob_env trans all_procs unsafe applied_trans systrans in*)
    
  let smost,smtime,overall =
    Hashtbl.fold (fun k (el,envoo) (ak, ael,overall) ->
      (*Format.printf "State: %d seen %d time(s)@." k el;*)
      (*if el > 1 then Format.printf "State: %d -- %a@." k  print_interpret_env envoo;*)
      if el > ael then (k,el,overall+el) else (ak,ael,overall+el)) hh (0,0,0) in
  
  (*Hashtbl.iter (fun k (el,envoo) ->
    Format.eprintf "State: %d, env: %a@." k print_interpret_env envoo) hh;*)
  
  Format.printf "Total entries: %d\n\
                 Total visited: %d\n\
                 State seen most often: %d [%d time(s)] @."
    (Hashtbl.stats hh).num_bindings overall smost smtime;
  
  Array.iteri (fun i a -> Format.eprintf "Proc %d : %d times@." (i+1) a) pc;

  Hashtbl.iter (fun k el -> Format.eprintf "Transition %a : %d times@." Hstring.print k el) tc;
  let num = Hashtbl.fold (fun k el acc -> el+acc) tc 0 in
  Format.eprintf "Total transitions taken: %d@." num;
  let num = float (num-1)  in 
  Hashtbl.iter (fun (k,k1) el -> Format.eprintf "(%a->%a) : %d (%f) @." Hstring.print k Hstring.print k1 el ((float el)/.num)) matrix;
  Format.eprintf "Corresp-@.";
  Array.iter (fun ((t,p),i) -> Format.eprintf" %a(%a) -> %d@."
    Hstring.print t.tr_name Variable.print_vars p i) tr_array;
  Format.eprintf "@.";
  Format.eprintf "HIST@.";
  Array.iter (fun x -> Format.eprintf" %f, " x) hist;
  Format.eprintf "@.";
  Format.eprintf "LNG@.";
  Array.iter (fun x -> Format.eprintf" %f, " x) lng;
  Format.eprintf "@."

