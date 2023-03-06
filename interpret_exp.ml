open Interpret_calc
open Interpret_types
open Interpret_errors
open Ast
open Types



let cumulative_prob probs =
  let _, l = List.fold_right (fun (n,el) (s,acc) -> let s1 = el+.s in s1,(n,s1)::acc) probs (0.,[])
  in List.rev l


let rec pick f l = 
match l with 
  | [] -> assert false 
  | (v,p)::tl -> if f <= p then v else pick f tl;;

  
let propose array elements = assert false
  

let markov glob tsys all_procs tr trans=
  Random.self_init ();
  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in 
  let matrix = create_transition_hash tsys in
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

  let before = Hstring.make "Init" in
  let before = ref before in
  
  let running = ref true in
  let running_env = ref glob in

  let des_ureqs = tr.tr_ureq in
  
  let w1 = ref 1 in 

  while !running do
    try
      let env, _,_,_ = !running_env in 
      let rand = Random.int els in
      let (proposal,prop_procs) = tr_array.(rand) in
      
      
      
      let sigma = Variable.build_subst proposal.tr_args prop_procs in
      
      (*check_actor_suspension sigma !global_env proposal.tr_process;*)
      
      check_reqs proposal.tr_reqs env sigma proposal.tr_name;
      let trargs = List.map (fun x -> Variable.subst sigma x) proposal.tr_args in
      let ureqs = uguard  sigma all_procs trargs proposal.tr_ureq in
      List.iter (fun u -> check_reqs u env sigma proposal.tr_name) ureqs;

      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in

      let nureqs = uguard sigma all_procs prop_procs des_ureqs in
      let reqq = SAtom.subst sigma tr.tr_reqs in
      let d1 = weight_env temp_env reqq env 0 in
	(*List.fold_left (fun acc1 el ->
	  let sigma' = Variable.build_subst tr.tr_args el in
	  let p = SAtom.subst sigma' des_reqs in 
	  (weight_env temp_env p env 0) + acc1) 0 des_procs in *)
      let d2 = 
	List.fold_left(fun acc satom ->
	  weight_env temp_env satom env acc) 0 nureqs in
      let w2 = d1+d2 in

      
      let flag =
	if w2 > !w1 then true else
	  begin
	    let fw1 = float !w1 in
	    let fw2 = float w2 in 
	    (*Format.eprintf "w1: %d, w2: %d, delta:%d@." !w1 w2 (w2 - !w1);*)
	    let prob = 2.718281828**((fw2-.fw1) /. 1.5) in
	      (*fw2/.fw1 in*)
	  let rand_prob = Random.float 1.0 in
	  if prob > rand_prob then true else false 
	end
      in
      if flag then
	begin
	  w1 := w2;
	  running_env := temp_env;

	  let pair = (!before, proposal.tr_name) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found ->
	      Hashtbl.add matrix pair 1
	  end;
	  
	  before := proposal.tr_name;
	  
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
	  
	end
	  
    with
      | TopError Deadlock -> running := false
      | TopError (FalseReq _) -> ()
      | Stdlib.Sys.Break -> running := false
      | Stdlib.Exit -> running := false
  done;
  !running_env, (hcount,proc_count, t_count, matrix)


(*----------------------*)
let markov_entropy glob tsys all_procs tr trans steps=
  Random.self_init ();
  let tried = ref 0 in
  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in 
  let matrix = create_transition_hash tsys in
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
  
  let running = ref true in
  let running_env = ref glob in

  let accept = ref 0  in
  let reject = ref 0 in
  
  let w1 = ref (entropy_env glob trans all_procs) in 

  while  (!taken < steps) && !running do
    try
      let env, _,_,_ = !running_env in 
      let rand = Random.int els in
      let (proposal,prop_procs) = tr_array.(rand) in
      
      
      
      let sigma = Variable.build_subst proposal.tr_args prop_procs in
      
      (*check_actor_suspension sigma !global_env proposal.tr_process;*)
      
      check_reqs proposal.tr_reqs env sigma proposal.tr_name;
      let trargs = List.map (fun x -> Variable.subst sigma x) proposal.tr_args in
      let ureqs = uguard  sigma all_procs trargs proposal.tr_ureq in
      List.iter (fun u -> check_reqs u env sigma proposal.tr_name) ureqs;

      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in
      tried := 0;

      
      let w2 = entropy_env temp_env trans all_procs in 

      
      let flag =
	if w2 > !w1 then
	  begin
	    Format.eprintf "---@.";
	    true
	  end
	else
	  begin
	    Format.eprintf "+++@.";
	    
	    (*Format.eprintf "w1: %d, w2: %d, delta:%d@." !w1 w2 (w2 - !w1);*)
	    let prob = 2.718281828**(w2 -. !w1) in
	      (*fw2/.fw1 in*)
	    let rand_prob = Random.float 1.0 in
	    (*Format.eprintf "old: %f , new: %f\nrand : %f, prob: %f@." !w1 w2 rand_prob prob;*)
	  if prob > rand_prob then true else false 
	end
      in
      if flag then
	begin

	  incr accept;
	  w1 := w2;
	  running_env := temp_env;
	  let pair = (!before, proposal.tr_name) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found ->
	      Hashtbl.add matrix pair 1
	  end;
	  before := proposal.tr_name;
	  
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
	  incr reject
	end;
      (*else*)
	(*begin
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
	  
	end;*)
      incr taken
    with
      | TopError Deadlock -> raise (TopError Deadlock)
      | TopError (FalseReq _) -> incr tried; incr taken; if !tried > 1000 then running := false 
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> running := false
  done;
  Format.eprintf "Accept: %d, Reject: %d@." !accept !reject;
  !running_env, (hcount,proc_count, t_count, matrix)


(*-----------------------*)
let markov_entropy_detailed glob tsys all_procs tr trans steps=
  Random.self_init ();
  let tried = ref 0 in
  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in 
  let matrix = create_detailed_hash tsys all_procs in
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
  
  let running = ref true in
  let running_env = ref glob in

  let accept = ref 0  in
  let reject = ref 0 in
  
  let w1 = ref (entropy_env glob trans all_procs) in 

  while  (!taken < steps) && !running do
    try
      let env, _,_,_ = !running_env in 
      let rand = Random.int els in
      let (proposal,prop_procs) = tr_array.(rand) in
      
      
      
      let sigma = Variable.build_subst proposal.tr_args prop_procs in
      
      (*check_actor_suspension sigma !global_env proposal.tr_process;*)
      
      check_reqs proposal.tr_reqs env sigma proposal.tr_name;
      let trargs = List.map (fun x -> Variable.subst sigma x) proposal.tr_args in
      let ureqs = uguard  sigma all_procs trargs proposal.tr_ureq in
      List.iter (fun u -> check_reqs u env sigma proposal.tr_name) ureqs;

      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in
      tried := 0;

      
      let w2 = entropy_env temp_env trans all_procs in 

      
      let flag =
	if w2 > !w1 then
	  begin
	    Format.eprintf "---@.";
	    true
	  end
	else
	  begin
	    Format.eprintf "+++@.";
	    
	    (*Format.eprintf "w1: %d, w2: %d, delta:%d@." !w1 w2 (w2 - !w1);*)
	    let prob = 2.718281828**(w2 -. !w1) in
	      (*fw2/.fw1 in*)
	    let rand_prob = Random.float 1.0 in
	    (*Format.eprintf "old: %f , new: %f\nrand : %f, prob: %f@." !w1 w2 rand_prob prob;*)
	  if prob > rand_prob then true else false 
	end
      in
      let prop_hs = trans_proc_to_hstring proposal.tr_name prop_procs in 
      if flag then
	begin
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
	      let htc= Hashtbl.find t_count prop_hs in
	      Hashtbl.replace t_count prop_hs (htc+1)
	    with Not_found -> Hashtbl.add t_count prop_hs 1
	  end ;
	end
      else
	begin
	  incr reject
	end;
      (*else*)
	(*begin
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
	  
	end;*)
      incr taken
    with
      | TopError Deadlock -> raise (TopError Deadlock)
      | TopError (FalseReq _) -> incr tried; incr taken; if !tried > 1000 then running := false 
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> running := false
  done;
  Format.eprintf "Accept: %d, Reject: %d@." !accept !reject;
  !running_env, (hcount,proc_count, t_count, matrix)

    


(*====*)
let markov_biased_proposal glob tsys all_procs tr trans steps=
  Random.self_init ();
  let tried = ref 0 in
  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in 
  let matrix = create_transition_hash tsys in
  let hprop = Hashtbl.create (List.length tsys) in(*proposition hash*)
  List.iter (fun x -> Hashtbl.add hprop x.tr_name []) tsys;
  let trt =
    List.fold_left (fun acc el->
      let args = el.tr_args in
      let num_args = List.length args in
      let tr_procs = all_arrange num_args all_procs in
      if tr_procs = [] then
	begin
	  Hashtbl.add hprop el.tr_name [[]];
	  (el,[])::acc
	end 
	  
      else
	begin
	  List.fold_left (fun acc_t procs ->
	    let l = Hashtbl.find hprop el.tr_name in
	    Hashtbl.replace hprop el.tr_name (procs::l);
	    (el, procs)::acc_t      
	  ) acc tr_procs
	
	end 
    ) [] tsys
  in

  (*Hashtbl.iter (fun k el ->
    Format.eprintf "@.";
    Format.eprintf "transition %a:@." Hstring.print k;
    List.iter (fun x -> Format.eprintf "%a@." Variable.print_vars x) el  
    ) hprop;*)
  let propositions = Hashtbl.create (List.length tsys) in 
  Hashtbl.iter (fun k el -> Hashtbl.add propositions k (List.length el, Array.of_list el)) hprop;

(*
  Hashtbl.iter (fun k (len, el) ->
    Format.eprintf "--@.";
    Format.eprintf "transition %a, #%d@." Hstring.print k len;
    Array.iter (fun x -> Format.eprintf "%a@." Variable.print_vars x) el  
  ) propositions;*)
 
  
  let els = List.length trt in 
  let tr_array = Array.of_list trt in

  let taken = ref 0 in
  
  let before = Hstring.make "Init" in
  let before = ref before in
  
  let running = ref true in
  let running_env = ref glob in

  let accept = ref 0  in
  let reject = ref 0 in

  let proposal_probs = [Hstring.make "t", 0.1; Hstring.make "t1", 0.4; Hstring.make "t2", 0.4; Hstring.make "t4", 0.1] in

  let cumulative_proposal = cumulative_prob proposal_probs in 
  
  
  let w1 = ref (entropy_env glob trans all_procs) in 

  while  (!taken < steps) && !running do
    try
      let env, _,_,_ = !running_env in 
      (*let rand = Random.int els in
	let (proposal,prop_procs) = tr_array.(rand) in*)

      let rand = Random.float 1. in 
      let choice = pick rand cumulative_proposal in 
      
      let elts, potent_tr = Hashtbl.find propositions choice in
      let rand_el = Random.int elts in
      let proposal, prop_procs = Trans.find choice trans, potent_tr.(rand_el) in 
      
      
      let sigma = Variable.build_subst proposal.tr_args prop_procs in
      
      (*check_actor_suspension sigma !global_env proposal.tr_process;*)
      
      check_reqs proposal.tr_reqs env sigma proposal.tr_name;
      let trargs = List.map (fun x -> Variable.subst sigma x) proposal.tr_args in
      let ureqs = uguard  sigma all_procs trargs proposal.tr_ureq in
      List.iter (fun u -> check_reqs u env sigma proposal.tr_name) ureqs;

      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in
      tried := 0;

      
      let w2 = entropy_env temp_env trans all_procs in 

      
      let flag =
	if w2 > !w1 then
	  begin
	    Format.eprintf "---@.";
	    true
	  end
	else
	  begin
	    Format.eprintf "+++@.";
	    
	    (*Format.eprintf "w1: %d, w2: %d, delta:%d@." !w1 w2 (w2 - !w1);*)
	    let prob = 2.718281828**(w2 -. !w1) in
	      (*fw2/.fw1 in*)
	    let rand_prob = Random.float 1.0 in
	    (*Format.eprintf "old: %f , new: %f\nrand : %f, prob: %f@." !w1 w2 rand_prob prob;*)
	  if prob > rand_prob then true else false 
	end
      in
      if flag then
	begin

	  incr accept;
	  w1 := w2;
	  running_env := temp_env;
	  let pair = (!before, proposal.tr_name) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found ->
	      Hashtbl.add matrix pair 1
	  end;
	  before := proposal.tr_name;
	  
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
	  incr reject
	end;
      (*else*)
	(*begin
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
	  
	end;*)
      incr taken
    with
      | TopError Deadlock -> raise (TopError Deadlock)
      | TopError (FalseReq _) -> incr tried; incr taken; if !tried > 1000 then running := false 
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> running := false
  done;
  Format.eprintf "Accept: %d, Reject: %d@." !accept !reject;
  !running_env, (hcount,proc_count, t_count, matrix)

    
    

(*==Biased entropy==*)
    let markov_biased_entropy glob tsys all_procs tr trans steps=
  Random.self_init ();
  let tried = ref 0 in
  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in 
  let matrix = create_transition_hash tsys in
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
  
  let running = ref true in
  let running_env = ref glob in

  let accept = ref 0  in
  let reject = ref 0 in
  
  let w1 = ref (entropy_env glob trans all_procs) in

  let proposal_probs = [Hstring.make "t", 0.1; Hstring.make "t1", 0.7; Hstring.make "t2", 0.1; Hstring.make "t4", 0.1] in

  while  (!taken < steps) && !running do
    try
      let env, _,_,_ = !running_env in 
      let rand = Random.int els in
      let (proposal,prop_procs) = tr_array.(rand) in
      
      
      
      let sigma = Variable.build_subst proposal.tr_args prop_procs in
      
      (*check_actor_suspension sigma !global_env proposal.tr_process;*)
      
      check_reqs proposal.tr_reqs env sigma proposal.tr_name;
      let trargs = List.map (fun x -> Variable.subst sigma x) proposal.tr_args in
      let ureqs = uguard  sigma all_procs trargs proposal.tr_ureq in
      List.iter (fun u -> check_reqs u env sigma proposal.tr_name) ureqs;

      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in
      tried := 0;

      
      let w2 = biased_entropy_env temp_env trans all_procs proposal_probs in 

      
      let flag =
	if w2 > !w1 then
	  begin
	    Format.eprintf "---@.";
	    true
	  end
	else
	  begin
	    Format.eprintf "+++@.";
	    
	    (*Format.eprintf "w1: %d, w2: %d, delta:%d@." !w1 w2 (w2 - !w1);*)
	    let prob = 2.718281828**(w2 -. !w1) in
	      (*fw2/.fw1 in*)
	    let rand_prob = Random.float 1.0 in
	    (*Format.eprintf "old: %f , new: %f\nrand : %f, prob: %f@." !w1 w2 rand_prob prob;*)
	  if prob > rand_prob then true else false 
	end
      in
      if flag then
	begin

	  incr accept;
	  w1 := w2;
	  running_env := temp_env;
	  let pair = (!before, proposal.tr_name) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found ->
	      Hashtbl.add matrix pair 1
	  end;
	  before := proposal.tr_name;
	  
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
	  incr reject
	end;
      (*else*)
	(*begin
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
	  
	end;*)
      incr taken
    with
      | TopError Deadlock -> raise (TopError Deadlock)
      | TopError (FalseReq _) -> incr tried; incr taken; if !tried > 1000 then running := false 
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> running := false
  done;
  Format.eprintf "Accept: %d, Reject: %d@." !accept !reject;
  !running_env, (hcount,proc_count, t_count, matrix)


    
(*=== Biased entropy and proposal ===*)

let markov_biased_entropy_biased_proposal glob tsys all_procs tr trans steps=
  Random.self_init ();
  let tried = ref 0 in
  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in 
  let matrix = create_transition_hash tsys in
  let hprop = Hashtbl.create (List.length tsys) in(*proposition hash*)
  List.iter (fun x -> Hashtbl.add hprop x.tr_name []) tsys;
  let trt =
    List.fold_left (fun acc el->
      let args = el.tr_args in
      let num_args = List.length args in
      let tr_procs = all_arrange num_args all_procs in
      if tr_procs = [] then
	begin
	  Hashtbl.add hprop el.tr_name [[]];
	  (el,[])::acc
	end 
	  
      else
	begin
	  List.fold_left (fun acc_t procs ->
	    let l = Hashtbl.find hprop el.tr_name in
	    Hashtbl.replace hprop el.tr_name (procs::l);
	    (el, procs)::acc_t      
	  ) acc tr_procs
	
	end 
    ) [] tsys
  in

  (*Hashtbl.iter (fun k el ->
    Format.eprintf "@.";
    Format.eprintf "transition %a:@." Hstring.print k;
    List.iter (fun x -> Format.eprintf "%a@." Variable.print_vars x) el  
    ) hprop;*)
  let propositions = Hashtbl.create (List.length tsys) in 
  Hashtbl.iter (fun k el -> Hashtbl.add propositions k (List.length el, Array.of_list el)) hprop;

(*
  Hashtbl.iter (fun k (len, el) ->
    Format.eprintf "--@.";
    Format.eprintf "transition %a, #%d@." Hstring.print k len;
    Array.iter (fun x -> Format.eprintf "%a@." Variable.print_vars x) el  
  ) propositions;*)
 
  
  let els = List.length trt in 
  let tr_array = Array.of_list trt in

  let taken = ref 0 in
  
  let before = Hstring.make "Init" in
  let before = ref before in
  
  let running = ref true in
  let running_env = ref glob in

  let accept = ref 0  in
  let reject = ref 0 in

  let proposal_probs = [Hstring.make "t", 0.1; Hstring.make "t1", 0.35; Hstring.make "t2", 0.35; Hstring.make "t4", 0.1] in

  let cumulative_proposal = cumulative_prob proposal_probs in 
  
  
  let w1 = ref (entropy_env glob trans all_procs) in 

  while  (!taken < steps) && !running do
    try
      let env, _,_,_ = !running_env in 
      (*let rand = Random.int els in
	let (proposal,prop_procs) = tr_array.(rand) in*)

      let rand = Random.float 1. in 
      let choice = pick rand cumulative_proposal in 
      
      let elts, potent_tr = Hashtbl.find propositions choice in
      let rand_el = Random.int elts in
      let proposal, prop_procs = Trans.find choice trans, potent_tr.(rand_el) in 
      
      
      let sigma = Variable.build_subst proposal.tr_args prop_procs in
      
      (*check_actor_suspension sigma !global_env proposal.tr_process;*)
      
      check_reqs proposal.tr_reqs env sigma proposal.tr_name;
      let trargs = List.map (fun x -> Variable.subst sigma x) proposal.tr_args in
      let ureqs = uguard  sigma all_procs trargs proposal.tr_ureq in
      List.iter (fun u -> check_reqs u env sigma proposal.tr_name) ureqs;

      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in
      tried := 0;

      
      let w2 = biased_entropy_env temp_env trans all_procs proposal_probs in 

      
      let flag =
	if w2 > !w1 then
	  begin
	    Format.eprintf "---@.";
	    true
	  end
	else
	  begin
	    Format.eprintf "+++@.";
	    
	    (*Format.eprintf "w1: %d, w2: %d, delta:%d@." !w1 w2 (w2 - !w1);*)

	    let bef =
	      begin
		try List.assoc !before proposal_probs
		with Not_found -> 0.000001
	      end
	    in
	    let hastings = (List.assoc proposal.tr_name proposal_probs ) /. bef in 
	    let prob = (2.718281828**(w2 -. !w1)) *. hastings in

	  	      (*fw2/.fw1 in*)
	    let rand_prob = Random.float 1.0 in
	    (*Format.eprintf "old: %f , new: %f\nrand : %f, prob: %f@." !w1 w2 rand_prob prob;*)
	  if prob > rand_prob then true else false 
	end
      in
      if flag then
	begin

	  incr accept;
	  w1 := w2;
	  running_env := temp_env;
	  let pair = (!before, proposal.tr_name) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found ->
	      Hashtbl.add matrix pair 1
	  end;
	  before := proposal.tr_name;
	  
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
	  incr reject
	end;
      (*else*)
	(*begin
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
	  
	end;*)
      incr taken
    with
      | TopError Deadlock -> raise (TopError Deadlock)
      | TopError (FalseReq _) -> incr tried; incr taken; if !tried > 1000 then running := false 
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> running := false
  done;
  Format.eprintf "Accept: %d, Reject: %d@." !accept !reject;
  !running_env, (hcount,proc_count, t_count, matrix)


(*==Hastings==*)


let markov_hastings glob tsys all_procs tr trans steps=
  Random.self_init ();
  let tried = ref 0 in
  let hcount = Hashtbl.create 10 in
  let proc_count = Array.make (Options.get_interpret_procs ()) 0 in
  let t_count = Hashtbl.create 10 in 
  let matrix = create_transition_hash tsys in
  let hprop = Hashtbl.create (List.length tsys) in(*proposition hash*)
  List.iter (fun x -> Hashtbl.add hprop x.tr_name []) tsys;

  let trt =
    List.fold_left (fun acc el->
      let args = el.tr_args in
      let num_args = List.length args in
      let tr_procs = all_arrange num_args all_procs in
      if tr_procs = [] then
	begin
	  Hashtbl.add hprop el.tr_name [[]];
	  (el,[])::acc
	end 
	  
      else
	begin
	  List.fold_left (fun acc_t procs ->
	    let l = Hashtbl.find hprop el.tr_name in
	    Hashtbl.replace hprop el.tr_name (procs::l);
	    (el, procs)::acc_t      
	  ) acc tr_procs
	
	end 
    ) [] tsys
  in

  

  (*Hashtbl.iter (fun k el ->
    Format.eprintf "@.";
    Format.eprintf "transition %a:@." Hstring.print k;
    List.iter (fun x -> Format.eprintf "%a@." Variable.print_vars x) el  
    ) hprop;*)
  let propositions = Hashtbl.create (List.length tsys) in 
  Hashtbl.iter (fun k el -> Hashtbl.add propositions k (List.length el, Array.of_list el)) hprop;


  Hashtbl.iter (fun k (len, el) ->
    Format.eprintf "--@.";
    Format.eprintf "transition %a, #%d@." Hstring.print k len;
    Array.iter (fun x -> Format.eprintf "%a@." Variable.print_vars x) el  
  ) propositions;
 
  let taken = ref 0 in
  
  let before = Hstring.make "Init" in
  let before = ref before in
  
  let running = ref true in
  let running_env = ref glob in

  let accept = ref 0  in
  let reject = ref 0 in

  (*let proposal_probs = [Hstring.make "t", 0.1; Hstring.make "t1", 0.4; Hstring.make "t2", 0.4; Hstring.make "t4", 0.1] in*)

  (* let proposal_probs = [Hstring.make "t", 0.026; Hstring.make "t1", 0.35; Hstring.make "t2", 0.35; Hstring.make "t4", 0.274] in*)

   let proposal_probs = [Hstring.make "t", 0.135; Hstring.make "t1", 0.35; Hstring.make "t2", 0.35; Hstring.make "t4", 0.165] in

  let cumulative_proposal = cumulative_prob proposal_probs in 
  
  
  let w1 = ref (entropy_env glob trans all_procs) in 

  while  (!taken < steps) && !running do
    try
      let env, _,_,_ = !running_env in 
      (*let rand = Random.int els in
	let (proposal,prop_procs) = tr_array.(rand) in*)

      let rand = Random.float 1. in 
      let choice = pick rand cumulative_proposal in 
      (*Format.eprintf "choice: %a@." Hstring.print choice;*)
      let elts, potent_tr = Hashtbl.find propositions choice in
      (*Format.eprintf "%d@." elts;*)
      let rand_el = Random.int elts in
      let proposal, prop_procs = Trans.find choice trans, potent_tr.(rand_el) in 
      
      
      let sigma = Variable.build_subst proposal.tr_args prop_procs in
      
      (*check_actor_suspension sigma !global_env proposal.tr_process;*)
      
      check_reqs proposal.tr_reqs env sigma proposal.tr_name;
      let trargs = List.map (fun x -> Variable.subst sigma x) proposal.tr_args in
      let ureqs = uguard  sigma all_procs trargs proposal.tr_ureq in
      List.iter (fun u -> check_reqs u env sigma proposal.tr_name) ureqs;

      let temp_env = apply_transition prop_procs proposal.tr_name trans !running_env in
      tried := 0;

      
      let w2 = entropy_env temp_env trans all_procs in 

      
      let flag =
	if w2 > !w1 then
	  begin
	    Format.eprintf "---@.";
	    true
	  end
	else
	  begin
	    Format.eprintf "+++@.";
	    
	    (*Format.eprintf "w1: %d, w2: %d, delta:%d@." !w1 w2 (w2 - !w1);*)
	    let bef =
	      begin
		try List.assoc !before proposal_probs
		with Not_found -> 0.000001
	      end
		in
	    let hastings = (List.assoc proposal.tr_name proposal_probs ) /. bef in 
	    let prob = (2.718281828**(w2 -. !w1)) *. hastings in
	      (*fw2/.fw1 in*)
	    let rand_prob = Random.float 1.0 in
	    (*Format.eprintf "old: %f , new: %f\nrand : %f, prob: %f@." !w1 w2 rand_prob prob;*)
	  if prob > rand_prob then true else false 
	end
      in
      if flag then
	begin

	  incr accept;
	  w1 := w2;
	  running_env := temp_env;
	  let pair = (!before, proposal.tr_name) in
	  begin
	    try
	      let cpair = Hashtbl.find matrix pair in
	      Hashtbl.replace matrix pair (cpair+1)
	    with Not_found ->
	      Hashtbl.add matrix pair 1
	  end;
	  before := proposal.tr_name;
	  
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
	  incr reject
	end;
      (*else*)
	(*begin
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
	  
	end;*)
      incr taken
    with
      | TopError Deadlock -> raise (TopError Deadlock)
      | TopError (FalseReq _) -> incr tried; incr taken; if !tried > 1000 then running := false 
      | Stdlib.Sys.Break -> taken := steps
      | Stdlib.Exit -> running := false
  done;
  Format.eprintf "Accept: %d, Reject: %d@." !accept !reject;
  !running_env, (hcount,proc_count, t_count, matrix)


    
    
    
let run glob tsys all_procs tr trans =
  let e, (hh,pc,tc,matrix)  =
    (*markov_entropy glob tsys all_procs tr trans 1000000*)
  (*markov_biased_proposal glob tsys all_procs tr trans 1000000*)
  (*markov_biased_entropy glob tsys all_procs tr trans 1000000*)
  (*markov_biased_entropy_biased_proposal glob tsys all_procs tr trans 1000000*)
  (*markov_hastings glob tsys all_procs tr trans 1000000*)
    markov_entropy_detailed glob tsys all_procs tr trans 1000000
    
  in
  let smost,smtime,overall =
    Hashtbl.fold (fun k (el,envoo) (ak, ael,overall) ->
      if el > ael then (k,el,overall+el) else (ak,ael,overall+el)) hh (0,0,0) in
  
  Format.printf "Total entries: %d\n\
                 Total visited: %d\n\
                 State seen most often: %d [%d time(s)] @."
    (Hashtbl.stats hh).num_bindings overall smost smtime;
  
  Array.iteri (fun i a -> Format.eprintf "Proc %d : %d times@." (i+1) a) pc;
	  
  Hashtbl.iter (fun k el -> Format.eprintf "Transition %a : %d times@." Hstring.print k el) tc;
  let num = Hashtbl.fold (fun k el acc -> el+acc) tc 0 in
  Format.eprintf "Total transitions taken: %d@." num;
  let num = float (num-1)  in 
  Hashtbl.iter (fun (k,k1) el -> Format.eprintf "%a->%a : %d @." Hstring.print k Hstring.print k1 el ) matrix;
  Format.eprintf "%a@." print_interpret_env e;
  let init_h = Hstring.make "Init" in 
  let dfile = Filename.basename Options.file in
  let current_time = string_of_float (Unix.time()) in
  let data_log = dfile^current_time^"data" in
  let open_file = open_out data_log in
  let ff = Format.formatter_of_out_channel open_file in
  Hashtbl.iter (fun (k,k1) el ->
    if Hstring.equal init_h k || Hstring.equal init_h k1 then ()
    else 
    Format.fprintf ff "%a->%a : %d@." Hstring.print k Hstring.print k1 el ) matrix;
  close_out open_file;
  Format.printf "File %s created@." data_log 

