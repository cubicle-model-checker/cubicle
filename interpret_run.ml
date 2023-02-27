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



let run glob_env trans all_procs unsafe applied_trans systrans=

  let hh = Hstring.make "A" in
  let hhh = Hstring.make "B" in 
  
  let q, e, (hh,pc,tc,matrix) =
    execute_random3 glob_env trans all_procs unsafe applied_trans systrans in
  let smost,smtime,overall =
    Hashtbl.fold (fun k (el,envoo) (ak, ael,overall) ->
      (*Format.printf "State: %d seen %d time(s)@." k el;*)
      if el > 1 then Format.printf "State: %d -- %a@." k  print_interpret_env envoo;
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
  Hashtbl.iter (fun (k,k1) el -> Format.eprintf "(%a->%a) : %d (%f) @." Hstring.print k Hstring.print k1 el ((float el)/.num)) matrix

