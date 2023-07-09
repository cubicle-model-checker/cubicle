open Ast
open Types
open Interpret_errors
open Interpret_types


let eval_arith ta env ty =
  let term, im =
    match ta with
      | Arith(t, im) -> t, im
      | _ -> assert false
  in
  let c = int_of_consts im in
  match term with
    | Elem(_, SystemProcs) ->
      let vv = !sys_procs + c in 
      if is_semaphore ty then VSemaphore vv
      else if is_int ty then VInt vv
      else if is_real ty then VReal (float_of_int vv)
      else assert false
    | _ -> begin
      let v = Env.find term env in  
      match v.value with
	| VInt i -> VInt (c+i)
	| VReal i -> assert false
	| VSemaphore i -> VSemaphore (c+i)
	| _ ->assert false
  end


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


let var_list_to_hstring l =
  let rec aux l acc =
    match l with
      | [] -> acc^")"
      | [el] -> let s = Hstring.view el in acc^s^")"
      | hd::tl -> let s = Hstring.view hd in 
		  let a = acc^s^"," in aux tl a
  in aux l "(";;


let create_transition_hash t =
  (* **2 because it'll be building a hash of all the pairs*)
  let stemp = (float (List.length t))** 2. in
  let size = int_of_float stemp in

  let ht = Hashtbl.create size in
  let names = List.map (fun x -> x.tr_name) t in
  let names = (Hstring.make "Init") :: names in
  let all_combs = all_combs_as_pairs names in
  List.iter (fun x -> Hashtbl.add ht x 0) all_combs;
  ht

let create_transition_map t =
  let names = List.map (fun x -> x.tr_name) t in
  let names = (Hstring.make "Init") :: names in
  let all_combs = all_combs_as_pairs names in
  List.fold_left (fun acc x -> MatrixMap.add x 0 acc) MatrixMap.empty all_combs
  
let trans_proc_to_hstring t p =
  let t_name = Hstring.view t in
  let procs = var_list_to_hstring p in
  Hstring.make (t_name^procs)
    
let create_detailed_hash t procs =
  let trt =
    List.fold_left (fun acc el->
      let args = el.tr_args in
      let num_args = List.length args in
      let tr_procs = all_arrange num_args procs in
      if tr_procs = [] then
	  (el,[])::acc
      else
	begin
	  List.fold_left (fun acc_t procs ->
	    (el, procs)::acc_t      
	  ) acc tr_procs
	
	end 
    ) [] t
  in
  let l = List.map (fun (tr, p) -> trans_proc_to_hstring tr.tr_name p) trt
  in
  let l = (Hstring.make "Init") :: l in
  let size = int_of_float ((float (List.length l))** 2.) in
  let ht = Hashtbl.create size in
  let all_combs = all_combs_as_pairs l in
  List.iter (fun x -> Hashtbl.add ht x 0) all_combs;
  ht

    

let gen_array name procs = 
  List.fold_left (fun acc a ->
    let indexes = Variable.all_arrangements_arity a procs in
    List.fold_left (fun acc lp ->
      Access (a, lp):: acc)
      acc indexes)
    [] [name]

let gen_array_eq_proc name procs = 
  List.fold_left (fun acc a ->
    let indexes = Variable.all_arrangements_arity a procs in
    List.fold_left (fun acc lp ->
      (Access (a, lp),lp):: acc)
      acc indexes)
    [] [name]

let gen_array_combs name procs = 
  List.fold_left (fun acc a ->
    let indexes = Variable.all_arrangements_arity a procs in
    List.fold_left (fun acc lp ->
      lp:: acc)
      acc indexes)
    [] [name]      

      
let check_unsafe_prover (env,_,_,_) unsafe =
  (*unsafe = (loc * variable * satom) list *)
  let procs = Variable.give_procs (Options.get_interpret_procs ()) in 
  let v = Env.fold (fun key {value = el} acc ->
    match el with
      | VGlob el -> SAtom.add (Comp(key, Eq, Elem(el, Glob))) acc 
      | VProc el -> SAtom.add (Comp(key, Eq, Elem(el, Var))) acc
      | VConstr el -> SAtom.add (Comp(key, Eq, Elem(el, Constr))) acc
      | VAccess(el,vl) -> SAtom.add (Comp(key, Eq, Access(el, vl))) acc
      | _-> acc   
  ) env SAtom.empty
  in
  List.iter (fun (_,vs, satom) ->
    let all_procs = Variable.all_permutations vs procs in
    List.iter (fun pl ->
      try
	let sa = SAtom.subst pl satom in
	Prover.reached vs v sa; raise (TopError Reached)
      with
	| Smt.Unsat  _ -> ()
	| TopError Reached -> raise (TopError Unsafe)
    ) all_procs      
  ) unsafe

exception UnsafeSeen

let comp_uns me term list =
  let rec aux l  =
    match l with
      | [] -> true 
      | hd::tl ->
	if Term.compare term hd = 0 then aux tl 
	else false
  in aux list

let check_unsafe1 glob unsafes =
  let env, _,_,_ = glob in  assert false
  (*unsafe = (loc * variable * satom) list *)
  
  

    
let check_unsafe glob unsafes =
  let env, _,_,_ = glob in
  (*unsafe = (loc * variable * satom) list *)
  let v = Env.fold (fun key {value = el} acc ->
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
  in
  List.iter (fun satom  ->
    if SAtom.subset satom v then raise (TopError Unsafe)
  ) unsafes 



let hash_queue q =
  let rec aux q h =
    if PersistentQueue.is_empty q then h
    else
      begin
	let x,r = PersistentQueue.pop q in
	let h1 = 13 * Types.Term.hash x in
	aux r (h + h1)
      end
  in aux q 0

    
let hash_locks locks =
  let v =
    LockQueues.fold (fun key el acc ->
      let v = hash_queue el in
      abs (19 * acc + (Term.hash key + v))
    ) locks 0
  in
  abs v

let hash_cond cond =
  let v =
    Conditions.fold(fun key el acc ->
      let h1 = List.fold_left (fun acc1 ll ->
	13 * acc1 + Term.hash ll) (Term.hash key) el
      in
      abs (19 * acc + h1)
    ) cond 0
  in abs v


let hash_sem sem =
  let v =
    Semaphores.fold(fun key el acc ->
      let h1 = List.fold_left (fun acc1 ll ->
	13 * acc1 + Term.hash ll) (Term.hash key) el
      in
      abs (19 * acc + h1)
    ) sem 0
  in abs v
  
    
let hash_e2nv env=
  let v =
    Env.fold (fun key {value = el; typ = typ } acc ->
      (*Format.eprintf "key: %a; typ: %a@." Term.print key Hstring.print typ;*)
      let h = 
	match el with
	  | VInt i -> (*let g = *)Hashtbl.hash i (*in Format.eprintf "hashed int %d: %d@." i g; g*) 
	  | VReal f -> Hashtbl.hash f 
	  | VBool b -> Hashtbl.hash b
	  | VConstr hs | VProc hs | VGlob hs -> (*let g = Hstring.hash hs in
						  Format.eprintf "hashed constr %a: %d@." Hstring.print hs g;g*)
	    Hstring.hash hs
	  | VAccess (hs,hsl) ->
	    List.fold_left (fun acc x -> 13 * acc + Hstring.hash x) (Hstring.hash hs) hsl
	  | VLock (b,topt) -> 
	    let h1 = Hashtbl.hash b in
	    begin
	      match topt with
		| None -> Hashtbl.hash None + h1
		| Some t -> Types.Term.hash t + h1
	    end
	  | VRLock (b,topt,i) ->
	    let h1 = Hashtbl.hash b + Hashtbl.hash i in 
	    begin
	      match topt with
		| None -> Hashtbl.hash None + h1
		| Some t -> Types.Term.hash t + h1
	    end
	  | VSemaphore i -> Hashtbl.hash i
	  | VArith t -> Types.Term.hash t
	  | _ -> 0 
	  (*| VSleep i -> Hashtbl.hash i
	  | _ -> Hashtbl.hash el  (*VAlive,VSuspended,UNDEF*)	*)  
      in
      abs (19 * acc + (Types.Term.hash key (*+ Hstring.hash typ *)+ h))
    ) env 0   
  in
  abs v


let hash_env env=
  let v =
    Env.fold (fun key {value = el; typ = typ } acc ->
      let h = 
	match el with
	  | VInt i -> 
	    if Options.num_range_up < i then Options.set_num_range_up i;
	    i 
	  | VReal f -> let f = string_of_float f in Hashtbl.hash f
	  | VBool b -> Hashtbl.hash b
	  | VConstr hs | VProc hs | VGlob hs -> 
	    Hstring.hash hs
	  | VAccess (hs,hsl) ->
	    List.fold_left (fun acc x -> 13 * acc + Hstring.hash x) (Hstring.hash hs) hsl
	  | VLock (b,topt) -> 
	    let h1 = if b then 17 else 31 in
	    begin
	      match topt with
		| None -> h1
		| Some t -> Types.Term.hash t + h1
	    end
	  | VRLock (b,topt,i) ->
	    let h1 = if b then 17 else 31 in 
	    let h1 = h1 + i in 
	    begin
	      match topt with
		| None -> h1
		| Some t -> Types.Term.hash t + h1
	    end
	  | VSemaphore i -> i
	  | VArith t -> Types.Term.hash t
	  | _ -> acc 
      in
      (19 * acc + 23 *Types.Term.hash key + 7*h)
    ) env 0   
  in
  abs v
    

let hash_loud_env env=
  let v =
    Env.fold (fun key {value = el; typ = typ } acc ->
      Format.eprintf "Hashing %a@." Term.print key;
      let h = 
	match el with
	  | VInt i -> Hashtbl.hash i 
	  | VReal f -> Hashtbl.hash f 
	  | VBool b -> Hashtbl.hash b
	  | VConstr hs | VProc hs | VGlob hs -> 
	    Hstring.hash hs
	  | VAccess (hs,hsl) ->
	    List.fold_left (fun acc x -> 13 * acc + Hstring.hash x) (Hstring.hash hs) hsl
	  | VLock (b,topt) -> 
	    let h1 = Hashtbl.hash b in
	    begin
	      match topt with
		| None -> Hashtbl.hash None + h1
		| Some t -> Types.Term.hash t + h1
	    end
	  | VRLock (b,topt,i) ->
	    let h1 = Hashtbl.hash b + Hashtbl.hash i in 
	    begin
	      match topt with
		| None -> Hashtbl.hash None + h1
		| Some t -> Types.Term.hash t + h1
	    end
	  | VSemaphore i -> Hashtbl.hash i
	  | VArith t -> Types.Term.hash t
	  | _ -> acc 
      in
      Format.eprintf "hashed %a == %d@." print_val el h;
      Format.eprintf "19*acc = %d\n23*Types.Term.hash = %d\n7*h = %d"
	(19 * acc) (23 * Types.Term.hash key) (7*h);
      let full = 
	(19 * acc + 23 *Types.Term.hash key + 7*h) in
      Format.eprintf "Full hash: %d@." full;
      full
    ) env 0   
  in
  abs v
    


let hash_full_env_loud (env,locks,cond,sem)=
  let v1 = hash_loud_env env in
  let v2 = hash_locks locks in
  let v3 = hash_cond cond in
  let v4 = hash_sem sem in
  Format.eprintf "v1: %d, v2: %d, v3: %d, v4: %d@." v1 v2 v3 v4;
  v1+v2+v3+v4
    

let hash_full_env (env,locks,cond,sem)=
  let v1 = hash_env env in
  let v2 = hash_locks locks in
  let v3 = hash_cond cond in
  let v4 = hash_sem sem in
  v1+v2+v3+v4
    


let add_sub_manip manip sigma =
  match manip with 
    | ProcManip([t], PlusOne) ->
      let t = Term.subst sigma t in 
      begin
	match t with
	  | Elem(n, Var) -> let ni = Variable.number n in
			    let ni = ni + 1 in
			    let ns = string_of_int ni in
			    let h = Hstring.make ("#"^ns) in
			    {value = VProc h; typ = Smt.Type.type_proc }
	  | _ -> assert false
      end
    | ProcManip([t], MinusOne) ->
      begin
	match t with
	  | Elem(n, Var) -> let ni = Variable.number n in
			    let ni = ni - 1 in
			    let ns = string_of_int ni in
			    let h = Hstring.make ("#"^ns) in
			    { value = VProc h; typ = Smt.Type.type_proc}
	  | _ -> assert false
      end
    | _ -> assert false



let check_req_comp t1 t2 env sigma op new_env =
  match t1, t2 with      
    | Elem(_, Glob), Elem(_, Glob) ->
	let ev1 = Env.find t1 env in
	let ev2 = Env.find t2 env in
      interpret_comp (compare_interp_val ev1 ev2) op	
    | Elem(_, Glob), Elem(_, (Constr|Var)) ->
      let ev1 = Env.find t1 env in
      let t2 = Term.subst sigma t2 in 
      interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op
	  
    | Elem (_, (Constr|Var)), Elem(_, Glob) ->
      let ev1 = Env.find t2 env in
      let t1 = Term.subst sigma t1 in 
      interpret_comp (compare_interp_val (to_interpret t1 ) ev1) op	
    | Elem(_, Glob), Access _ ->
      let t = Term.subst sigma t2 in
      let ev1 = Env.find t1 env in
      let ev2 = Env.find t env in
      interpret_comp (compare_interp_val ev1 ev2) op	
    | Access _, Elem(_, Glob) ->
      let t = Term.subst sigma t1 in
      let ev1 = Env.find t env in
      let ev2 = Env.find t2 env in
      interpret_comp (compare_interp_val ev1 ev2) op	
    | Elem (_, (Constr|Var)), Access _ ->
	
      let t = Term.subst sigma t2 in
      let ev1 = Env.find t env in
      let t1 = Term.subst sigma t1 in 
      interpret_comp (compare_interp_val (to_interpret t1 ) ev1) op	
	
    | Access _, Elem (_, (Constr|Var))->
      let t = Term.subst sigma t1 in
      let ev1 = Env.find t env in
      let t2 = Term.subst sigma t2 in 
      interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op
	
    | Elem(n1,Constr), Elem(n2,Constr) -> interpret_comp (Hstring.compare n1 n2) op

    | Access _, Const msc->
      let t = Term.subst sigma t1 in
      let ev1 = Env.find t env in
      let t2 = Term.subst sigma t2 in 
      interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op
	  
    | Elem(n1, Glob), Const msc ->
      let t1 = Term.subst sigma t1 in
      let ev1 = Env.find t1 env in
      interpret_comp (compare_interp_val ev1 (to_interpret t2)) op

    | Const msc , Elem(n1,Glob)->
      let t2 = Term.subst sigma t2 in
      let ev1 = Env.find t2 env in
      interpret_comp (compare_interp_val (to_interpret t1) ev1) op
	
	
    | Elem(n1, Glob), Arith(aterm, msc) ->
      let t1 = Term.subst sigma t1 in
      let ev1 = Env.find aterm env in
      interpret_comp (compare_interp_val ev1 (to_interpret t1)) op

    | Arith(aterm, msc), Elem(n1, Glob) ->
      let t2 = Term.subst sigma t2 in
      let ev1 = Env.find aterm env in
      interpret_comp (compare_interp_val ev1 (to_interpret t2)) op
    | Elem(p1, Var), Elem(p2, Var) ->
      let t1 = Term.subst sigma t1 in
      let t2 = Term.subst sigma t2 in
      interpret_comp (compare_interp_val (to_interpret t1) (to_interpret t2)) op
    | tt1, Elem(_, SystemProcs) ->
      let t1 = Term.subst sigma tt1 in
      interpret_comp (compare_interp_val (to_interpret t1) (to_interpret t2)) op
    | Elem(_,SystemProcs), tt1 ->
      let t2 = Term.subst sigma tt1 in
      interpret_comp (compare_interp_val (to_interpret t2) (to_interpret t1)) op

    | ProcManip _ , _ ->
      let t2 = Term.subst sigma t2 in
      let pt = add_sub_manip t1 sigma in
      interpret_comp (compare_interp_val pt (to_interpret t2)) op 
      
    | _, ProcManip  _ ->
      let t1 = Term.subst sigma t1 in
      let pt = add_sub_manip t2 sigma in
      interpret_comp (compare_interp_val (to_interpret t1) pt) op
    | Access _, Access _ ->
      let ev1 = Env.find t1 env in
      let ev2 = Env.find t2 env in
      interpret_comp (compare_interp_val ev1 ev2) op
	
    | _ -> Format.eprintf "sup: %a, %a@." Term.print t1 Term.print t2;assert false

let throwaway = Elem(Hstring.make "UNDEF", Glob)


let check_comp_req t1 t2 env sigma op =
  match t1, t2 with      
    | Elem(_, Glob), Elem(_, Glob) ->
      let ev1 =
	try
	  Some (Env.find t1 env)
	with Not_found -> None
      in
      let ev2 = 
	try
	  Some (Env.find t2 env)
	with Not_found -> None
      in
      begin
	match ev1, ev2 with
	  | None, None -> assert false
	  | Some ev1, Some ev2 -> interpret_comp (compare_interp_val ev1 ev2) op, env
	  | Some ev1, None -> true, (Env.add t2 ev1 env)
	  | None, Some ev2 -> true, (Env.add t1 ev2 env)
      end 
    | Elem(_, Glob), Elem(_, (Constr|Var)) ->
      let ev1 =
	try Some (Env.find t1 env)
	with Not_found -> None 
      in
      let t2 = Term.subst sigma t2 in

      begin
	match ev1 with
	  | None -> true, Env.add t1 (to_interpret t2) env
	  | Some ev1 -> interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op, env
      end 	  
    | Elem (_, (Constr|Var)), Elem(_, Glob) ->
      let ev1 =
	try Some (Env.find t2 env)
	with Not_found -> None
	      
      in
      let t1 = Term.subst sigma t1 in
      begin
	match ev1 with
	  | None -> true , Env.add t2 (to_interpret t1) env
	  | Some ev1 -> interpret_comp (compare_interp_val (to_interpret t1 ) ev1) op, env
      end 
      	
    | Elem(_, Glob), Access _ ->
      let t = Term.subst sigma t2 in     
      let ev1 =
	try Some (Env.find t1 env)
	with Not_found -> None
      in
      let ev2 =
	try
	  Some (Env.find t env)
	with Not_found -> None
      in
      begin
	match ev1, ev2 with
	  | None, None ->Format.eprintf "%a -- %a@." Term.print t1 Term.print t2; assert false
	  | Some ev1, Some ev2 -> interpret_comp (compare_interp_val ev1 ev2) op, env
	  | None, Some ev2 -> true, Env.add t1 (to_interpret t2) env
	  | Some ev1, None -> true, Env.add t (to_interpret t1) env 
      end 
    | Access _, Elem(_, Glob) ->
      let t = Term.subst sigma t1 in
      let ev1 =
	try
	  Some (Env.find t env)
	with Not_found -> None
      in
      let ev2 =
	try
	  Some(Env.find t2 env)
	with Not_found -> None
      in
      begin
	match ev1, ev2 with
	  | None, None -> assert false
	  | Some ev1, Some ev2 -> interpret_comp (compare_interp_val ev1 ev2) op, env
	  | None, Some ev2 -> true, Env.add t (to_interpret t2) env
	  | Some ev1, None -> true, Env.add t2 (to_interpret t) env 
      end
      
    | Elem (_, (Constr|Var)), Access _ ->
	
      let t = Term.subst sigma t2 in
      let ev1 =
	try
	  Some (Env.find t env)
	with Not_found -> None
      in
      let t1 = Term.subst sigma t1 in
      begin
	match ev1 with
	  | None -> true, Env.add t (to_interpret t1) env
	  | Some ev1 -> interpret_comp (compare_interp_val (to_interpret t1 ) ev1) op, env	

      end 
	
    | Access _, Elem (_, (Constr|Var))->
      let t = Term.subst sigma t1 in
      let ev1 =
	try
	  Some(Env.find t env)
	with Not_found -> None
      in
      let t2 = Term.subst sigma t2 in
      begin
	match ev1 with
	  | None -> true, Env.add t (to_interpret t2) env
	  | Some ev1 -> interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op, env
      end 
	
    | Elem(n1,Constr), Elem(n2,Constr) -> interpret_comp (Hstring.compare n1 n2) op, env

    | Access _, Const msc->
      let t = Term.subst sigma t1 in
      let ev1 =
	try
	  Some (Env.find t env)
	with Not_found -> None
      in
      let t2 = Term.subst sigma t2 in
      begin
	match ev1 with
	  | None -> true, Env.add t (to_interpret t2) env
	  | Some ev1 -> interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op, env
      end 	  
    | Elem(n1, Glob), Const msc ->
      let t1 = Term.subst sigma t1 in
      let ev1 =
	try Some (Env.find t1 env)
	with Not_found -> None
      in
      begin
	match ev1 with
	  | None -> true, Env.add t1 (to_interpret t2) env
	  | Some ev1 -> interpret_comp (compare_interp_val ev1 (to_interpret t2)) op, env
      end 
    | Const msc , Elem(n1,Glob)->
      let t2 = Term.subst sigma t2 in
      let ev1 =
	try
	  Some (Env.find t2 env)
	with Not_found -> None
      in
      begin
	match ev1 with
	  | None -> true, Env.add t2 (to_interpret t1) env
	  | Some ev1 -> interpret_comp (compare_interp_val (to_interpret t1) ev1) op, env
      end 	
	
    | Elem(n1, Glob), Arith(aterm, msc) ->
      let t1 = Term.subst sigma t1 in
      let ev1 =
	try
	  Some (Env.find aterm env)
	with Not_found -> None 
      in
      begin
	match ev1 with
	  | None -> true, Env.add t1 (to_interpret t2) env
	  | Some ev1 -> interpret_comp (compare_interp_val ev1 (to_interpret t1)) op, env
      end 
    | Arith(aterm, msc), Elem(n1, Glob) ->
      let t2 = Term.subst sigma t2 in
      let ev1 =
	try
	  Some (Env.find aterm env)
	with Not_found -> None
      in
      begin
	match ev1 with
	  | None -> true, Env.add t2 (to_interpret t1) env
	  | Some ev1 -> interpret_comp (compare_interp_val ev1 (to_interpret t2)) op, env
      end 
      
    | Elem(p1, Var), Elem(p2, Var) ->
      let t1 = Term.subst sigma t1 in
      let t2 = Term.subst sigma t2 in
      interpret_comp (compare_interp_val (to_interpret t1) (to_interpret t2)) op, env
	
    | tt1, Elem(_, SystemProcs) ->
      let t1 = Term.subst sigma tt1 in
      interpret_comp (compare_interp_val (to_interpret t1) (to_interpret t2)) op, env
    | Elem(_,SystemProcs), tt1 ->
      let t2 = Term.subst sigma tt1 in
      interpret_comp (compare_interp_val (to_interpret t2) (to_interpret t1)) op, env

    | ProcManip _ , _ ->
      let t2 = Term.subst sigma t2 in
      let pt = add_sub_manip t1 sigma in
      interpret_comp (compare_interp_val pt (to_interpret t2)) op , env
      
    | _, ProcManip  _ ->
      let t1 = Term.subst sigma t1 in
      let pt = add_sub_manip t2 sigma in
      interpret_comp (compare_interp_val (to_interpret t1) pt) op, env
	
    | Access _, Access _ ->
      let t1 = Term.subst sigma t1 in
      let t2 = Term.subst sigma t2 in
      (*let ev1 = Env.find t1 env in
      let ev2 = Env.find t2 env in
	interpret_comp (compare_interp_val ev1 ev2) op*)
      let ev1 =
	try
	  Some (Env.find t1 env)
	with Not_found -> None
      in
      let ev2 = 
	try
	  Some (Env.find t2 env)
	with Not_found -> None
      in
      begin
	match ev1, ev2 with
	  | None, None -> assert false
	  | Some ev1, Some ev2 -> interpret_comp (compare_interp_val ev1 ev2) op, env
	  | Some ev1, None -> true, (Env.add t2 ev1 env)
	  | None, Some ev2 -> true, (Env.add t1 ev2 env)
      end 
    | _ -> Format.eprintf "sup: %a, %a@." Term.print t1 Term.print t2;assert false

      
      

let check_comp t1 t2 env sigma op =
  match t1, t2 with      
    | Elem(_, Glob), Elem(_, Glob) ->
      let ev1 = Env.find t1 env in
      let ev2 = Env.find t2 env in
      interpret_comp (compare_interp_val ev1 ev2) op	
    | Elem(_, Glob), Elem(_, (Constr|Var)) ->
      let ev1 = Env.find t1 env in
      let t2 = Term.subst sigma t2 in 
      interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op
	  
    | Elem (_, (Constr|Var)), Elem(_, Glob) ->
      let ev1 = Env.find t2 env in
      let t1 = Term.subst sigma t1 in 
      interpret_comp (compare_interp_val (to_interpret t1 ) ev1) op	
    | Elem(_, Glob), Access _ ->
      let t = Term.subst sigma t2 in
      let ev1 = Env.find t1 env in
      let ev2 = Env.find t env in
      interpret_comp (compare_interp_val ev1 ev2) op	
    | Access _, Elem(_, Glob) ->
      let t = Term.subst sigma t1 in
      let ev1 = Env.find t env in
      let ev2 = Env.find t2 env in
      interpret_comp (compare_interp_val ev1 ev2) op	
    | Elem (_, (Constr|Var)), Access _ ->
	
      let t = Term.subst sigma t2 in
      let ev1 = Env.find t env in
      let t1 = Term.subst sigma t1 in 
      interpret_comp (compare_interp_val (to_interpret t1 ) ev1) op	
	
    | Access _, Elem (_, (Constr|Var))->
      let t = Term.subst sigma t1 in
      let ev1 = Env.find t env in
      let t2 = Term.subst sigma t2 in 
      interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op
	
    | Elem(n1,Constr), Elem(n2,Constr) -> interpret_comp (Hstring.compare n1 n2) op

    | Access _, Const msc->
      let t = Term.subst sigma t1 in
      let ev1 = Env.find t env in
      let t2 = Term.subst sigma t2 in 
      interpret_comp (compare_interp_val ev1 (to_interpret t2 )) op
	  
    | Elem(n1, Glob), Const msc ->
      let t1 = Term.subst sigma t1 in
      let ev1 = Env.find t1 env in
      interpret_comp (compare_interp_val ev1 (to_interpret t2)) op

    | Const msc , Elem(n1,Glob)->
      let t2 = Term.subst sigma t2 in
      let ev1 = Env.find t2 env in
      interpret_comp (compare_interp_val (to_interpret t1) ev1) op
	
	
    | Elem(n1, Glob), Arith(aterm, msc) ->
      let t1 = Term.subst sigma t1 in
      let ev1 = Env.find aterm env in
      interpret_comp (compare_interp_val ev1 (to_interpret t1)) op

    | Arith(aterm, msc), Elem(n1, Glob) ->
      let t2 = Term.subst sigma t2 in
      let ev1 = Env.find aterm env in
      interpret_comp (compare_interp_val ev1 (to_interpret t2)) op
    | Elem(p1, Var), Elem(p2, Var) ->
      let t1 = Term.subst sigma t1 in
      let t2 = Term.subst sigma t2 in
      interpret_comp (compare_interp_val (to_interpret t1) (to_interpret t2)) op
    | tt1, Elem(_, SystemProcs) ->
      let t1 = Term.subst sigma tt1 in
      interpret_comp (compare_interp_val (to_interpret t1) (to_interpret t2)) op
    | Elem(_,SystemProcs), tt1 ->
      let t2 = Term.subst sigma tt1 in
      interpret_comp (compare_interp_val (to_interpret t2) (to_interpret t1)) op

    | ProcManip _ , _ ->
      let t2 = Term.subst sigma t2 in
      let pt = add_sub_manip t1 sigma in
      interpret_comp (compare_interp_val pt (to_interpret t2)) op 
      
    | _, ProcManip  _ ->
      let t1 = Term.subst sigma t1 in
      let pt = add_sub_manip t2 sigma in
      interpret_comp (compare_interp_val (to_interpret t1) pt) op
    | Access _, Access _ ->
      let ev1 = Env.find t1 env in
      let ev2 = Env.find t2 env in
      interpret_comp (compare_interp_val ev1 ev2) op	
    | _ -> Format.eprintf "sup: %a, %a@." Term.print t1 Term.print t2;assert false

    
let check_reqs reqs env sigma tname=
  let glob = ref env in 
  SAtom.iter (fun atom ->
    match atom with
      | Comp (t1,op,t2) ->
	if Options.debug_interpreter then
	  begin
	    let t11 = Term.subst sigma t1 in
	    let t21 = Term.subst sigma t2 in 
	    Format.eprintf "Checking requirements, comparing t1 and t2: %a -- %a@." Term.print t11 Term.print t21;
	  end;
	let b, nv = check_comp_req t1 t2 !glob sigma op in
	glob := nv; 
	if b  then ()
	else raise (TopError (FalseReq tname))		
      | True -> ()
      | False ->  raise (TopError (FalseReq tname))
      | Ite _ -> assert false
  ) reqs;
  !glob



let check_switches swts env name sigma  =
  let env = ref env in
  List.fold_left (fun (acc,flag) (sa, t) ->
    let v=
      SAtom.fold (fun atom acc2 ->
	match atom with
	  | Comp(t1, op, t2) ->
	    begin
	      match t1,t2 with
		  (*TODO : check that this works if multiple procs in transitiions*)
		| Elem(n1,Var), Elem(n2,Var) -> assert false
		| Elem(n1,Var), _ ->
		  let g =
		    try List.assoc n1 sigma with
			Not_found -> assert false 
		  in
		  let b,me = check_comp_req (Elem(g, Var)) t2 !env sigma op in
		  env := me;
		   b && acc2
		|  _, Elem(n1,Var) ->

		  let g =
		    try List.assoc n1 sigma with
			Not_found -> assert false 
		  in
		  let b,me = check_comp_req (Elem(g, Var)) t1 !env sigma op in
		  env := me;
		  b && acc2
		| _ ->
		  let b,me = check_comp_req t1 t2 !env sigma op in
		  env := me;
		  b && acc2
	  end 
	  | True -> true && acc2
	  | False -> false && acc2
	  | _ -> assert false		
    ) sa true in
    if v && not flag then
      (Env.add name (to_interpret (Term.subst sigma t) ) !env , v)  
    else 
    (acc,flag)  
  ) (!env,false) swts 
      
	

let update_vals env assigns sigma =
  let env = ref env in 
  List.fold_left (fun acc (name, assign) ->
    let elem = Elem(name, Glob) in
    match assign with
      | UTerm t ->
	begin
	  match t with
	    | Elem (n, Glob) | Access (n,_) ->
	      begin
		let v =
		  try Env.find (Term.subst sigma t) !env
		  with Not_found ->
		    begin
		      let _,ty = Smt.Symbol.type_of n in
		      let new_el = {value = random_value ty; typ = ty } in
 		      new_el
		    end
		in
		env := Env.add t v !env;
		let acc = Env.add t v acc in
		Env.add elem v acc
	      end 
	    | Arith(t', cs) ->
	      let i_cs = int_of_consts cs in
	      let t_sub = Term.subst sigma t' in 
	      let {value = v; typ = typ} = Env.find t_sub !env in
	      let v' = match v with
		| VInt vi -> VInt (vi + i_cs) |  _ -> assert false in	      
	      Env.add elem {value = v';  typ = typ} acc
	    | Elem(n,Var) -> Env.add elem (to_interpret (Term.subst sigma t)) acc
	      
	    | ProcManip ([t], addsub ) -> let t = Term.subst sigma t in
					Env.add elem (to_interpret (ProcManip([t],addsub))) acc
	    | _ ->
	      
	      Env.add elem (to_interpret (Term.subst sigma t)) acc
	end 
      | UCase t ->
	fst (check_switches t !env elem sigma )
  (* (Satom.t * term ) list --> c1 : t1 ...*)
  ) !env assigns 

let upd_arr_direct sigma orig upd tname =
  let (ups, upt) = List.hd upd.up_swts in
  let atoms = SAtom.elements ups in
  match atoms with
    | [Atom.Comp(t1, op, Elem(n,Var))] ->
      let elem = Access(tname, [n]) in
      let t = Term.subst sigma elem in
      begin
	match upt with
	  | Elem(n, Glob) -> let t2, more =
			       try
				 Env.find upt orig, None
			       with Not_found ->
				 begin
				   let _,ty = Smt.Symbol.type_of n in
				   let new_el = {value = random_value ty; typ = ty } in
 				   new_el, Some (upt, new_el)
				 end
			     in
			     t, t2, more
	  | Access (na, _ ) -> let upt = Term.subst sigma upt in
			let t2, more =
			  try Env.find upt orig, None
			  with Not_found ->
			    begin
			      let _,ty = Smt.Symbol.type_of na in
			      let new_el = {value = random_value ty; typ = ty } in
 			      new_el, Some (upt, new_el)
			    end
			
			in
			t, t2, more
	  | ProcManip ([tpm], addsub) -> let tt = Term.subst sigma tpm in
					 t, (to_interpret (ProcManip([tt],addsub))), None
	  | Arith(t', cs) ->
	    begin
	      
	      try
		let i_cs = int_of_consts cs in
		let t_sub = Term.subst sigma t' in
		let {value = v; typ = typ} = Env.find t_sub orig in
		let v' = match v with
		  | VInt vi -> VInt (vi + i_cs) |  _ -> assert false in
		let new_el = { value = v'; typ = typ }
		in
		t, new_el, Some(t_sub,new_el)
	      with
		  Not_found ->
		    assert false
	    end 
	    
	  | _ -> t, (to_interpret (Term.subst sigma upt)), None
      end 
      | _ -> assert false


(*X[k] := case | i = k -> case where you compare generale with proc in args *)
(*let create_case_proc op accatom g side h all_procs term upd =
  match op with
    | Eq ->			  
      begin   
	let temp = Access(upd.up_arr, [g]) in
	Hashtbl.replace h g true;
	Env.add temp (to_interpret term ) accatom		      		 
      end, true
    | Lt ->
      List.fold_left (fun tacc el ->
	let b = 
	  if side then Hstring.compare g el
	  else Hstring.compare el g in 
	if b = -1 then
	  begin
	    Hashtbl.replace h el true;
	    let temp = Access(upd.up_arr, [el]) in
	    Env.add temp (to_interpret term ) tacc 
	  end
	else tacc 
      ) accatom all_procs, true
    | Le ->
      List.fold_left (fun tacc el ->
	let b = 
	  if side then Hstring.compare g el
	  else Hstring.compare el g in  
	if b = -1 || b = 0 then
	  begin
	    Hashtbl.replace h el true;
	    let temp = Access(upd.up_arr, [el]) in
	    Env.add temp (to_interpret term ) tacc 
	  end
	else tacc 
      ) accatom all_procs, true
    | Neq ->
      List.fold_left (fun tacc el ->			    
	if Hstring.compare g el = 0 then
	  tacc
	else 
	  begin
	    Hashtbl.replace h el true;
	    let temp = Access(upd.up_arr, [el]) in
	    Env.add temp (to_interpret term ) tacc 
	  end
	    
      ) accatom all_procs, true

let check_proc_comparison n1 n2 sigma op accatom upd term h all_procs =
  let g1, fg1 =
    try List.assoc n1 sigma, true
    with Not_found -> Hstring.make "", false
  in
  let g2, fg2 =
    try List.assoc n2 sigma, true
    with Not_found -> Hstring.make "", false
  in
  match fg1, fg2 with
    | false, false -> assert false
    | true, false -> create_case_proc op accatom g1 true h all_procs term upd
    | false, true -> create_case_proc op accatom g2 false h all_procs term upd
    | true, true ->
      begin
	match op with
	  | Eq ->
	    if Hstring.compare g1 g2 = 0 then
	      List.fold_left (fun tacc el ->
		Hashtbl.replace h el true;
		let temp = Access(upd.up_arr, [el]) in
		Env.add temp (to_interpret term ) tacc) accatom all_procs, true
	    else accatom, false
	  | Neq ->
	    if Hstring.compare g1 g2 <> 0 then
	      List.fold_left (fun tacc el ->
		Hashtbl.replace h el true;
		let temp = Access(upd.up_arr, [el]) in
		Env.add temp (to_interpret term ) tacc) accatom all_procs, true
	    else accatom,false
	  | _ -> assert false (*TODO*)
	     
      end *)
 
let switchy_satoms op g1 g2 sacc =
  match op with
    | Eq ->
      if Hstring.compare g1 g2 = 0 then true && sacc
      else false && sacc 
    | Neq ->
      if Hstring.compare g1 g2 <> 0 then true && sacc
      else false && sacc 
    | Lt ->
      if Hstring.compare g1 g2 = -1 then true && sacc
      else false && sacc 
    | Le ->
      let b = Hstring.compare g1 g2 in
      if  b = -1 || b = 0 then true && sacc
      else false && sacc 

let upd_array_case sigma orig upd tname env =
  let orig = ref orig in
  let env = ref env in 
  let all_procs = Variable.give_procs (Options.get_interpret_procs ()) in 
  (*List.iter (fun x -> Format.eprintf "pre filter: %a@." Hstring.print x) all_procs;*)
  (*let all_procs = List.filter (fun x ->
    let elem = Elem(x, Var) in
    let v = Env.find elem env in
    v.value = VAlive) all_procs in*)
  (*List.iter (fun x -> Format.eprintf "Post filter: %a@." Hstring.print x) all_procs;*)
  let swts = upd.up_swts in
  List.fold_left (fun acc proc ->
      let added = ref [] in 

    let e, _ = 
      List.fold_left (fun (acc2,f) (sa,t) ->
	let t = 
	match t with
	  | Access(n,[pl]) ->
	    begin
	      let pl' =
		try
		  List.assoc pl sigma
		with Not_found -> proc
	      in
	      let elem = (Access(n,[pl'])) in
	      begin
		try 
		  Env.find elem !orig
		with Not_found -> 
		  begin
		    let _,ty = Smt.Symbol.type_of n in
		    let new_el = {value = random_value ty; typ = ty } in
		    (*orig := Env.add elem new_el !orig;
		    env := Env.add elem new_el !env;*)
		    added := (elem, new_el)::!added;
 		    new_el
		  end 
	      end 
	    end
	  | Access (n,[pl1;pl2]) ->
	    begin
	      let pl1' =
		try
		  List.assoc pl1 sigma
		with Not_found -> proc
	      in
	      let pl2' =
		try
		  List.assoc pl2 sigma
		with Not_found -> proc
	      in
	      let elem = (Access(n,[pl1';pl2'])) in
	      try 
		Env.find elem !orig
	      with Not_found -> 
		begin
		  let _,ty = Smt.Symbol.type_of n in
		  let new_el = {value = random_value ty; typ = ty } in
		  (*orig := Env.add elem new_el !orig;
		  env := Env.add elem new_el !env;*)
		  added := (elem, new_el)::!added;
 		  new_el
		end 
	    end 
	  | Elem(n, Glob) ->
	    begin
	      try 
		Env.find t !orig (*NOTE: changed from env to orig*)
	      with Not_found ->
		begin
		  let _,ty = Smt.Symbol.type_of n in
		  let new_el = {value = random_value ty; typ = ty } in
		  (*orig := Env.add t new_el !orig;
		  env := Env.add t new_el !env;*)
		  added := (t, new_el)::!added;
 		  new_el
		end 
	    end
	      
	  | Elem(np, Var) -> let tt = Variable.subst sigma np in {value = VProc tt; typ = Smt.Type.type_proc} 
	  | ProcManip([pmt], addsub) ->
	    let pmt = Term.subst sigma pmt in
	    to_interpret (ProcManip([pmt],addsub))
	  | _ -> to_interpret t
	in	
      let flag = 
	SAtom.fold (fun atom sacc ->
	  match atom with
	    | Comp (t1,op,t2) ->
	      begin
		match t1,t2 with
		  | Elem(n1,Var), Elem(n2, Var) ->
		  let g1 =
		    try Some (List.assoc n1 sigma)
		    with Not_found -> None
		  in
		  let g2 =
		    try Some (List.assoc n2 sigma)
		    with Not_found -> None
		  in
		  
		  begin
		    match g1, g2 with
		      | None, None -> assert false (*should not happen*)
			
		      | Some gn1, None -> switchy_satoms op gn1 proc sacc  && sacc
					
		      | None, Some gn1 -> switchy_satoms op proc gn1 sacc  && sacc
 
		      | Some gn1, Some gn2 -> switchy_satoms op gn1 gn2 sacc  && sacc	  			
		  end 

		  | Elem(n1,Var), _  ->
		    let g =
		      try List.assoc n1 sigma with
			  Not_found ->  proc
		    in
		    check_comp (Elem(g, Var)) t2 !orig sigma op  && sacc
		  | _, Elem(n1,Var) ->
		    let g =
		      try List.assoc n1 sigma with
			  Not_found ->  proc
		    in
		    check_comp t1 (Elem(g, Var)) !orig sigma op  && sacc
		      	    
		  | Access(n1, [pn1]), _ ->
		    let g =
		      try List.assoc pn1 sigma with
			Not_found -> proc
		    in
		    check_comp (Access(n1,[g])) t2 !orig sigma op  && sacc
		    
		  | _, Access(n1, [pn1]) ->
		    let g =
		      try List.assoc pn1 sigma with
			Not_found -> proc
		    in check_comp t1 (Access(n1,[g])) !orig sigma op && sacc(*DO THIS FOR MATRIX*)

		  | Access(n1, [pn1;pn2]), _ ->
		    let g =
		      try List.assoc pn1 sigma with
			Not_found -> proc
		    in
		    let g1 =
		      try List.assoc pn2 sigma with
			Not_found -> proc
		    in
		    check_comp (Access(n1,[g;g1])) t2 !orig sigma op  && sacc
		    
		  | _, Access(n1, [pn1;pn2]) ->
		    let g =
		      try List.assoc pn1 sigma with
			  Not_found -> proc
		    in
		    let g1 =
		      try List.assoc pn2 sigma with
			  Not_found -> proc
		    in check_comp t1 (Access(n1,[g;g1])) !orig sigma op && sacc
		    
		  | _ ->
		    (*let t1 = Term.subst sigma t1 in
		    let t2 = Term.subst sigma t2 in*) 
		    check_comp t1 t2 !orig sigma op && sacc
	    end
	  | True -> true && sacc
	  | False -> false && sacc
	  | Ite _ -> assert false	    
	) sa true	  
      in
      if flag && not f then
	begin
	  let temp = Access(upd.up_arr, [proc]) in
	  orig := List.fold_left (fun a (el, v) -> Env.add el v a) !orig !added;
	  env := List.fold_left (fun a (el, v) -> Env.add el v a) !env !added;  
	  let acc2 = List.fold_left (fun a (el, v) -> Env.add el v a) acc2 !added in 
	  Env.add temp t acc2, true
	end
      else
	 acc2, f
    ) (acc,false) swts
    in e  
  ) !env all_procs
  

let upd_matrix sigma orig upd env =
  let orig = ref orig in
  let env = ref env in 
  (*List.iter (fun x -> Format.eprintf "%a@." Hstring.print x) upd.up_arg;*)
  let s = Hstring.view (List.hd upd.up_arg) in
  let s1 = String.sub s 0 1 in
  let flag =  s1 = "_" in
  (*if flag then normal else case construct*)
  match flag with
    | true ->
      let added = ref [] in
      let e, _ = List.fold_left (fun (facc,fflag) (sa,t) ->	
	if not fflag then
	  begin
	    let p1,p2 =
	      SAtom.fold (fun sa acc ->
		match sa with
		  | Comp (t1,op,t2) ->
		    begin
		      match t1,t2 with		    
			| Elem(n1,Var), Elem(n2,Var) ->
			  begin
			    match acc with
			      | None,None -> Some n2, None
			      | Some _, Some _ -> assert false
			      | None, Some a -> assert false
			      | Some a, None -> Some a, Some n2
			  end 
			| _ -> assert false
		    end
		  | True -> acc 
		  | _ -> assert false
	      ) sa (None,None) 
	    in
	    match p1,p2 with
	      | Some a, Some b ->
		let elem = Term.subst sigma (Access(upd.up_arr, [a;b]))  in
		begin
		  let v = 
		    match t with
		      | Elem (n,Glob) ->
			begin
			  try
			    Env.find t !orig
			  with Not_found ->
			    begin
			      let _,ty = Smt.Symbol.type_of n in
			      let new_el = {value = random_value ty; typ = ty } in
			      (*orig := Env.add t new_el !orig;
				env := Env.add t new_el !env;*)
			      added := (t, new_el)::!added;
 			      new_el
			    end 
			    
			end
		      | Access (n,_) ->
			begin
			  let upt = Term.subst sigma t in
			  try
			    Env.find upt !orig
			  with
			      Not_found ->
				begin
				  let _,ty = Smt.Symbol.type_of n in
				  let new_el = {value = random_value ty; typ = ty } in
				  (*orig := Env.add t new_el !orig;
				    env := Env.add t new_el !env;*)
				  added := (t, new_el)::!added;
 				  new_el
				end 
			
			end
		      | _ -> to_interpret t
		  in
		  orig :=  List.fold_left (fun a (el, v) -> Env.add el v a) !orig !added;
		  env := List.fold_left (fun a (el, v) -> Env.add el v a) !env !added;
		  Env.add elem v facc, true 
		end 

		
		
	      | Some _, None -> assert false
	      | None, Some _ -> assert false
	      | None, None -> assert false
	  end
	else facc,fflag
      ) (!env,false) upd.up_swts
      in e
      
    | false ->
      let procs = Variable.give_procs (Options.get_interpret_procs ()) in
      (*List.iter (fun x -> Format.eprintf "pre filter: %a@." Hstring.print x) procs;*)
      (*let procs = List.filter (fun x ->
	let elem = Elem(x, Var) in
	let v = Env.find elem orig in
	(v.value = VAlive) ) procs in*)
      (*List.iter (fun x -> Format.eprintf "Post filter: %a@." Hstring.print x) procs;*thisone*)
      let all = gen_array_combs upd.up_arr procs in
      (*List.iter (fun x ->
	List.iter (fun y -> Format.eprintf "%a" Hstring.print y) x; Format.eprintf "@.")all;
      *)
      List.fold_left (fun acc procs ->
	let proc1,proc2 =
	  match procs with | [p1;p2] -> p1,p2 | _ -> assert false
	in
	let added = ref [] in
	let  e, _ =  
	  List.fold_left (fun (acc2, f) (sa,t) ->
	    let t = 
	      match t with
		| Access(n,[pl]) ->
		  begin
		    let pl' =
		      try
			List.assoc pl sigma
		      with Not_found ->
		        if Hstring.compare pl (List.hd upd.up_arg) = 0
			then proc1 else proc2
		    in
		    let el_m = (Access(n,[pl'])) in
		    (*Format.eprintf "el_m: %a@." Term.print el_m;*)
		    try
		      Env.find el_m !orig 
		      
		    with Not_found ->
		      begin
			let _,ty = Smt.Symbol.type_of n in
			let new_el = {value = random_value ty; typ = ty } in
			(*orig := Env.add el_m new_el !orig;
			env := Env.add el_m new_el !env;*)
			added := (el_m, new_el)::!added;
 			new_el
		      end
			
		  end
		| Access(n,[pl1;pl2]) ->
		  (*Format.eprintf "pl1: %a, pl2: %a@." Hstring.print pl1 Hstring.print pl2;
		  Format.eprintf "proc1: %a, proc2: %a@." Hstring.print proc1 Hstring.print proc2;
		  List.iter (fun (aa,bb) -> Format.eprintf "%a --> %a@." Hstring.print aa Hstring.print bb) sigma;*)
		  begin
		    let pl1' =
		      try
			List.assoc pl1 sigma
		      with Not_found ->
			if Hstring.compare pl1 (List.hd upd.up_arg) = 0
			then proc1 else proc2
		    in
		    let pl2' =
		      try
			List.assoc pl2 sigma
		      with Not_found ->
			if Hstring.compare pl2 (List.hd upd.up_arg) = 0
			then proc1 else proc2

		    in
		    let el_m = (Access(n,[pl1';pl2'])) in
		    try 
		      Env.find el_m !orig
		    with Not_found ->
		      begin
			let _,ty = Smt.Symbol.type_of n in
			let new_el = {value = random_value ty; typ = ty } in
			(*orig := Env.add el_m new_el !orig;
			env := Env.add el_m new_el !env;*)
			added := (el_m, new_el)::!added;
 			new_el
		      end 
		  end
		| Elem(n, Glob) ->
		  begin
		    try 
		      Env.find t !orig 
		    with Not_found ->
		      begin
			let _,ty = Smt.Symbol.type_of n in
			let new_el = {value = random_value ty; typ = ty } in
			(*orig := Env.add t new_el !orig;
			env := Env.add t new_el !env;*)
			added := (t, new_el)::!added;
 			new_el
		      end 
		  end
		| Elem(np, Var) ->
		  let tt = Variable.subst sigma np
		  in {value = VProc tt; typ = Smt.Type.type_proc} 
		| ProcManip([pmt], addsub) ->
		  let pmt = Term.subst sigma pmt in
		  to_interpret (ProcManip([pmt],addsub))
		| _ -> to_interpret t
	    in  
	  let flag =
	    SAtom.fold (fun atom sacc ->
	      match atom with
		| Comp (t1,op,t2)->
		  begin
		    (*Format.eprintf "comparing %a and %a@." Term.print t1 Term.print t2;*)
		    match t1, t2 with
		      | Elem(n1, Var), Elem(n2,Var) ->
			let proc1, proc2 = 
			  if Hstring.compare n1 (List.hd upd.up_arg) = 0
			  then proc1, proc2
			  else proc2, proc1 in 
			let g1 =
			  try Some (List.assoc n1 sigma)
			  with Not_found -> None
			in
			let g2 =
			  try Some (List.assoc n2 sigma)
			  with Not_found -> None
			in
			begin
			  
			  match g1, g2 with
			    | None, None ->
	        	      switchy_satoms op proc1 proc2 sacc			  
			    | Some gn1, None ->
			      switchy_satoms op gn1 proc2 sacc
			    | None, Some gn1 ->
			      switchy_satoms op proc1 gn1 sacc
			    | Some gn1, Some gn2 ->
			      switchy_satoms op gn1 gn2 sacc

			end
		      | Elem(n1, Var), _ ->
			let g =
			  try List.assoc n1 sigma with
			      Not_found ->
				if Hstring.compare n1 (List.hd upd.up_arg) = 0
				then proc1 else proc2
			in
			check_comp (Elem(g, Var)) t2 !orig sigma op  && sacc
		      | _, Elem(n1,Var) ->
			let g =
			  try List.assoc n1 sigma with
			      Not_found ->
				if Hstring.compare n1 (List.hd upd.up_arg) = 0
				then proc1 else proc2
			in
			check_comp t1 (Elem(g, Var)) !orig sigma op  && sacc
		      | Access(n1, [pn1]), _ ->
			let g =
			  try List.assoc pn1 sigma with
			      Not_found ->
				if Hstring.compare n1 (List.hd upd.up_arg) = 0
				then proc1 else proc2
			in
			check_comp (Access(n1,[g])) t2 !orig sigma op  && sacc

		      |Access(n1, [pn1;pn2]), _ ->
			let g =
			  try List.assoc pn1 sigma with
			      Not_found ->
				if Hstring.compare n1 (List.hd upd.up_arg) = 0
				then proc1 else proc2
			in
			let g1 =
			  try List.assoc pn2 sigma with
			      Not_found ->
				if Hstring.compare n1 (List.hd upd.up_arg) = 0
				then proc1 else proc2
			in 
			check_comp (Access(n1,[g;g1])) t2 !orig sigma op  && sacc


		      | _, Access(n1, [pn1;pn2]) ->
			let g =
			  try List.assoc pn1 sigma with
			      Not_found -> if Hstring.compare n1 (List.hd upd.up_arg) = 0
				then proc1 else proc2
			in
			let g1 =
			  try List.assoc pn1 sigma with
			      Not_found -> if Hstring.compare n1 (List.hd upd.up_arg) = 0
				then proc1 else proc2
			
			in check_comp t1 (Access(n1,[g;g1])) !orig sigma op && sacc
			

		      | _, Access(n1, [pn1]) ->
			let g =
			  try List.assoc pn1 sigma with
			      Not_found -> if Hstring.compare n1 (List.hd upd.up_arg) = 0
				then proc1 else proc2
			in check_comp t1 (Access(n1,[g])) !orig sigma op && sacc
			
			  
		      | _ -> check_comp t1 t2 !orig sigma op && sacc
		  (*other to elem*) (*TODO ADD OTHER COMPS*)			
			
		  end 		  
		| True -> true && sacc
		| False -> false && sacc
		| Ite _ -> assert false
	    ) sa true

	  in
	  if flag && not f then
	    begin
	      let temp = Access(upd.up_arr, procs) in
	      List.iter (fun (x,y) -> Format.eprintf "%a @." Term.print x) !added;
	      orig := List.fold_left (fun a (el, v) -> Env.add el v a) !orig !added;
	      env := List.fold_left (fun a (el, v) -> Env.add el v a) !env !added;   
	      let acc2 =  List.fold_left (fun a (el, v) -> Env.add el v a) acc2 !added 
	      in Env.add temp (*to_interpret*) t acc2, true
	    end 
	    else acc2, f
	) (acc,false) upd.up_swts
	in e  
      ) !env all

      
      
      
    
let update_arrs sigma orig acc upds =
  let orig = ref orig in 
  List.fold_left (fun acc1 upd ->
    let name = upd.up_arr in
    (*List.iter (fun x -> Format.eprintf "arg %a@." Hstring.print x) upd.up_arg;*)
    if List.length upd.up_arg = 1 then
      let s = Hstring.view (List.hd upd.up_arg) in
      let s1 = String.sub s 0 1 in
      if s1 = "_" then
	begin
	  let t, v, opt = upd_arr_direct sigma !orig upd name in
	  match opt with
	    | None -> Env.add t v acc1
	    | Some (el,v1) ->
	      orig := Env.add el v1 !orig;
	      let ev = Env.add t v acc1 in
	      Env.add el v1 ev  	  
	end
      else
	let e = (*upd_arr_case*) upd_array_case sigma !orig upd name acc1 in
	(*Env.add t v acc1 *) e
    else upd_matrix sigma !orig upd acc1    
  ) acc upds

      
let uguard sigma args tr_args = function
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
(*
let map_atoms a sigma =
  match a with
    | Atom.Comp(t1,op, t2) -> Atom.Comp(Term.subst sigma t1, op, Term.subst sigma t2)
    | Ite _ -> assert false
    | a -> a*)
    

let upd_non_dets env nondets =
  let proc = Hstring.make "proc" in
  List.fold_left (fun acc el ->
    Env.add (Elem(el, Glob)) {value = random_value proc; typ = proc} acc
  ) env nondets

let wait_unlock lockq lock_elem env =
  let q = LockQueues.find lock_elem lockq in
  if PersistentQueue.is_empty q then
    Env.add lock_elem {value = VLock(false,None); typ = ty_lock} env,
    lockq
  else
    let new_proc, rem_queue = PersistentQueue.pop q in
    let nv =
      Env.add lock_elem {value = VLock(true, Some new_proc); typ = ty_lock} env (*changed from ty_proc*)
    in
    let v = Env.find new_proc env in 
    let nv = Env.add new_proc {value = VAlive; typ = v.typ} nv in
    let lq = LockQueues.add lock_elem rem_queue lockq in nv,lq   
    
let update_locks_unlocks sigma env new_env tr lock_queue cond_sets semaphores=
  let locks = tr.tr_locks in
  (*let unlocks = tr.tr_unlocks in
  let wait = tr.tr_wait in
  let notify = tr.tr_notify in
  let notifyall = tr.tr_notifyall in*) 
  match locks with
    | [] -> new_env, lock_queue, cond_sets, semaphores
    | [Lock lockp] ->
      begin
	match lockp with
	  | VarLock(lock_elem,p) ->
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env  in
	    begin	      
	     match v.value  with
	       | VLock(b, po) ->
		 let term = Elem(Variable.subst sigma p, Var) in
		 let term_type = (Env.find term env).typ in 
		  if not b then
		    begin
		      (Env.add lock_elem
			 { value = VLock(true, Some term); typ = v.typ } new_env),
		      lock_queue,
		      cond_sets, semaphores
		    end		
		  else
		    begin
		      if po = None then assert false; (*TODO ERROR*)
		      (*if is_condition v.typ then
			deal_wait true lockp sigma env new_env tr lock_queue cond_sets else*)
		      let q = LockQueues.find lock_elem lock_queue in
		      let new_queue =  PersistentQueue.push term q in
		      let lock_queue = LockQueues.add lock_elem new_queue lock_queue in
		      (Env.add term {value = VSuspended; typ = term_type} new_env),
		      lock_queue,
		      cond_sets, semaphores
		    end
		| VRLock(b,po,i) ->
		  let term = Elem(Variable.subst sigma p, Var) in
		  if not b then
		    (Env.add lock_elem
		       { value = VRLock(true, Some term, 1); typ = v.typ } new_env),
		    lock_queue,
		    cond_sets, semaphores
		  else
		    begin
		      match po with
			| None -> assert false
			| Some p ->

			  let q = LockQueues.find lock_elem lock_queue in


			  if Term.compare p term = 0 then
			    
			    (Env.add lock_elem {value = VRLock(true, Some p,i+1); typ = v.typ} new_env), lock_queue, cond_sets, semaphores

			  else
			    begin
			      let term_type = (Env.find term env).typ in
			      let new_queue = PersistentQueue.push term q in
			      let lock_queue = LockQueues.add lock_elem new_queue lock_queue in
			      (Env.add term {value = VSuspended; typ = term_type} new_env), lock_queue, cond_sets, semaphores
			    end
			    
		    end
		| VSemaphore i ->
		  let term = Elem(Variable.subst sigma p, Var) in 

		  if i > 0 then
		    (Env.add lock_elem { value = VSemaphore(i-1); typ = v.typ} new_env), lock_queue, cond_sets, semaphores
		  else
		    let sl = Semaphores.find lock_elem semaphores in
		    let sema = Semaphores.add lock_elem (term::sl) semaphores in
		    let term_type = (Env.find term env).typ in
		    (Env.add term {value = VSuspended; typ = term_type} new_env), lock_queue, cond_sets, sema
   		| VGlob _ -> assert false
		| VProc _ -> assert false
		| VInt _ -> assert false
		| VReal _ -> assert false
		| VConstr _ -> assert false
		| VAccess _ -> assert false
		| VAlive -> assert false
		| _ -> assert false
	     
	    end
      
       
      end
      
    | [Unlock unlock]  ->
      begin
	match unlock with
	  | VarLock(lock_elem,p) ->
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env in
	    
	    let p_ask = Elem(Variable.subst sigma p, Var) in	     
	    begin
	      match v.value with
		| VLock(b,po) ->
		  if not b then new_env, lock_queue, cond_sets, semaphores
		  else
		    begin
		      match po with
			| None -> assert false
			| Some proc -> 
			  if Term.compare p_ask proc <> 0
			  then
			    let () = Format.eprintf
			      "@{<b>@{<fg_magenta>WARNING@}@}: Process %a cannot unlock %a's lock, release not applied@." Term.print p_ask Term.print proc in
			  new_env, lock_queue, cond_sets, semaphores
			  (*raise (TopError (CantUnlockOther(p_ask,proc)))*)
			  else 
			    begin
			      let q = LockQueues.find lock_elem lock_queue
			      in
			      if PersistentQueue.is_empty q then
				Env.add lock_elem {value = VLock(false,None); typ = v.typ} new_env,
				lock_queue, cond_sets, semaphores
			      else
				let new_proc, rem_procs = PersistentQueue.pop q in
				let nv =
				  Env.add
				    lock_elem {value = VLock(true, Some new_proc); typ = v.typ}
				    new_env
				in
				let term_type = (Env.find new_proc env).typ in
				let nv = Env.add new_proc {value = VAlive; typ = term_type} nv in
				let lq = LockQueues.add lock_elem rem_procs lock_queue in
				nv,lq, cond_sets, semaphores
			    end 
			  
		    end
		| VRLock(b,po,i) ->
		  if not b then new_env, lock_queue, cond_sets, semaphores
		  else
		    begin
		      match po with
			| None -> assert false
			| Some proc ->
			  if Term.compare p_ask proc <> 0
			  then
			    let () = Format.eprintf
			      "@{<b>@{<fg_magenta>WARNING@}@}: Process %a cannot unlock %a's lock, release not applied@." Term.print p_ask Term.print proc in
			    new_env, lock_queue, cond_sets, semaphores




			  (*raise (TopError (CantUnlockOther(p_ask,proc)));*)
			  else
			    begin
			  let q = LockQueues.find lock_elem lock_queue
			  in
			  if i = 1 then
			    if PersistentQueue.is_empty q then
			      Env.add lock_elem {value = VRLock(false,None,0); typ = v.typ} new_env,lock_queue, cond_sets, semaphores
			    else
			      let new_proc, rem_procs = PersistentQueue.pop q in
			      let nv =
				Env.add
				  lock_elem {value = VRLock(true, Some new_proc,1); typ = v.typ}
				  new_env
			      in
			      let term_type = (Env.find new_proc env).typ in 
			      let nv = Env.add new_proc {value = VAlive; typ = term_type} nv in
			      let lq = LockQueues.add lock_elem rem_procs lock_queue in
			      nv,lq, cond_sets, semaphores
			  else
			    Env.add lock_elem {value = VRLock(true, Some proc, i-1); typ = v.typ} new_env,
			    lock_queue , cond_sets, semaphores

		      end
		    end

		| VSemaphore i ->
		  let sl =  Semaphores.find lock_elem semaphores in
		  if sl = [] then
		    (Env.add lock_elem { value = VSemaphore(i+1); typ = v.typ} new_env), lock_queue, cond_sets, semaphores
		  else
		    let wakeup = List.hd sl in 
		    let sema = Semaphores.add lock_elem (List.tl sl) semaphores in
		    let term_type = (Env.find wakeup env).typ in
		    (Env.add wakeup {value = VAlive; typ = term_type} new_env), lock_queue, cond_sets, sema
		  
		| _ -> assert false
		  		
	    end 
	    
      end
    | [Wait wait] -> (*deal_wait false wait sigma env new_env tr lock_queue cond_sets*)    
     begin
	match wait with
	  | VarLock(lock_elem, p) ->
	    let term = Elem(Variable.subst sigma p, Var) in
	    let term_value = Env.find term env in 
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env in
	    begin
	      match v.value with
		| VLock(b,po) ->
		  begin
		    match po with
		      | None ->
			if b then assert false
			else
			  begin
			    match term_value.value with
			      | VSleep i -> if i > 0 then
				  (Env.add term {value = VSleep(i+1); typ = (Env.find term env).typ} new_env),
				lock_queue,
				cond_sets,
				semaphores
				else 
				  raise (TopError (CantWaitNeverLock (term, lock_elem)))
			      | VSuspended -> raise (TopError (SuspendedProc term))
			      | VAlive ->  raise (TopError (CantWaitNeverLock (term, lock_elem)))
			      | _ -> assert false
			  end 
		      | Some pr ->
			if not b then assert false
			else
			  begin
			    if Term.compare pr term = 0 then
			      let clist = Conditions.find lock_elem cond_sets in
			      let clist = term::clist in
			      let term_type = (Env.find term env).typ in
			      let nv, lq = wait_unlock lock_queue lock_elem new_env in
			      (Env.add term {value = VSleep 1; typ = term_type} nv),
			      lq,
			      Conditions.add lock_elem clist cond_sets,
			      semaphores
			    else
			      begin
				match term_value.value with
				  | VSleep i -> if i > 0 then
				      (Env.add term {value = VSleep(i+1); typ = (Env.find term env).typ} new_env),
				    lock_queue,
				    cond_sets,
				    semaphores
				    else 
				      raise (TopError (CantWaitNeverLock (term, lock_elem)))
				  | VSuspended -> raise (TopError (SuspendedProc term))
				  | VAlive ->  raise (TopError (CantWaitNeverLock (term, lock_elem)))
				  | _ -> 
				    assert false
			      end 
			      
			  end 
			
		  end
		  
		| _ -> assert false
	    end 
	
      end 
    | [Notify notify] ->
      begin
	match notify with
	  | VarLock(lock_elem,p) ->
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env in
	    let p_ask = Elem(Variable.subst sigma p, Var) in
	    begin
	      match v.value with
		| VLock(b,po) ->
		  if not b then raise (TopError UnlockedNotify);
		  begin
		    match po with
		      | None -> assert false
		      | Some pr ->
			if Term.compare pr p_ask <> 0 then
			(*raise (TopError (CantNotifyNotMine(p_ask, lock_elem)));*)
			  let() =
			    Format.eprintf
			      "Process %a can't notify: lock %a does not belong to %a@."
			      Term.print p_ask Term.print lock_elem Term.print p_ask in
			new_env, lock_queue, cond_sets,	semaphores
			else
			  begin
			    let waiting = Conditions.find lock_elem cond_sets in
			    if waiting = [] then new_env, lock_queue, cond_sets, semaphores
			    else
			      let cond_sets =
				Conditions.add lock_elem (List.tl waiting) cond_sets in
			      let q = LockQueues.find lock_elem lock_queue in
			      
			      let new_queue = PersistentQueue.push (List.hd waiting) q in
			      let t_term = List.hd waiting in
			      let term_type = (Env.find t_term env).typ in
			      let nv = Env.add t_term { value = VSuspended; typ = term_type} new_env in
			      let lq = LockQueues.add lock_elem new_queue lock_queue
			      in nv,lq,cond_sets, semaphores
			  end 
			    
			
		  
			  
			
		  end 
		| _ -> assert false		    
	    end
      end
	
    | [NotifyAll notifyall] ->
      begin
	match notifyall with
	  | VarLock(lock_elem,p) ->
	    let lock_elem = Term.subst sigma lock_elem in
	    let v = Env.find lock_elem env in
	    let p_ask = Elem(Variable.subst sigma p, Var) in
	    begin
	      match v.value with
		| VLock(b,po) ->
		  if not b then raise (TopError UnlockedNotify);
		  begin
		    match po with
		      | None -> assert false
		      | Some pr ->
			if Term.compare pr p_ask <> 0 then
			(*raise (TopError (CantNotifyNotMine(p_ask, lock_elem)));*)
			  let() =
			    Format.eprintf
			      "Process %a can't notify: lock %a does not belong to %a@."
			      Term.print p_ask Term.print lock_elem Term.print p_ask in
			new_env, lock_queue, cond_sets,	semaphores
			else
			  begin
			    let waiting = Conditions.find lock_elem cond_sets in
			    if waiting = [] then new_env, lock_queue, cond_sets, semaphores
			    else
			      let cond_sets =
				Conditions.add lock_elem [] cond_sets in
			      let q = LockQueues.find lock_elem lock_queue in
			      let nv =
				List.fold_left (fun acc el ->
				  let term_type = (Env.find el env).typ in
				  Env.add el {value = VSuspended; typ = term_type } acc) new_env waiting
			      in  
			      let new_queue = List.fold_left (fun acc el -> PersistentQueue.push el acc) q waiting in
			      let lq = LockQueues.add lock_elem new_queue lock_queue
			      in nv,lq,cond_sets, semaphores
			  end
		  end 
		| _ -> assert false		    
	    end
      end


      
    | _ -> assert false
  
let check_actor_suspension_sched sigma env actor desired_actor=
  match actor with
    | None -> false
    | Some p -> let elem = Term.subst sigma (Elem(p, Var)) in
		if Term.compare elem desired_actor = 0 then 
		  let v = Env.find elem env in
		  begin
		    match v.value with
		      | VAlive -> true
		      | VSuspended -> raise (TopError (SuspendedProc elem))
		      | VSleep _ -> raise (TopError (SleepingProc elem))
		      | _ -> assert false
		  end
		else false


let check_actor_suspension sigma env actor =
  match actor with
    | None -> ()
    | Some p -> let elem = Term.subst sigma (Elem(p, Var)) in
		
		let v = Env.find elem env in
		begin
		match v.value with
		  | VAlive -> ()
		  | VSuspended -> raise (TopError (SuspendedProc elem))
		  | VSleep _ -> raise (TopError (SleepingProc elem))
		  | _ -> assert false
		end

let check_subtype sigma env tr_args =
  List.iter (fun (v, hopt) ->
    match hopt with
      | None -> ()
      | Some subtype ->
	let elem = Elem(v, Var) in 
	let v = Term.subst sigma elem in
	let { typ = ty } = Env.find v env in
	if Hstring.equal subtype ty then ()
	else raise (TopError (BadSubType (v,subtype)))
  ) tr_args
      

let check_ureqs ureqs env sigma trname =
  let glob = ref env in 
  let rec aux ur =
    match ur with
      | [] -> raise (TopError (FalseReq trname))
      | hd::tl ->
	begin
	  try
	    glob := check_reqs hd !glob sigma trname
	  with
	    | TopError (FalseReq _) -> aux tl 
	end
  in aux ureqs;
  !glob


let apply_transition_forward args trname trans (env,lock_queue,cond_sets, semaphores) =
  let tr = Trans.find trname trans in
  let arg_length = List.length tr.tr_args in
  if List.length args <> arg_length then
    raise (TopError (WrongArgs (trname,arg_length)));

  let tr_args = List.map fst tr.tr_args in (* MODIFIED subsorts*)

  let sigma = Variable.build_subst tr_args args in 

  check_actor_suspension sigma env tr.tr_process;
  check_subtype sigma env tr.tr_args;

  (*let new_env = check_reqs tr.tr_reqs env sigma trname in
  let procs = Variable.give_procs (Options.get_interpret_procs ()) in
  let trargs = List.map (fun x -> Variable.subst sigma x) tr.tr_args in
  let ureqs = uguard sigma procs trargs tr.tr_ureq in
  (*List.iter (fun u -> Format.eprintf "checkingg : %a@." SAtom.print u) ureqs;*)
  (*Ureqs that have ORs are lists with multiple elements : no or means 1 el in list
    so instead of iter, it has to be a function because one of the elements has to satisfy 
  *)
  (*let () = List.iter (fun u -> check_reqs u env sigma trname) ureqs in*)
  let new_env = check_ureqs ureqs new_env sigma trname in *)
  let nv = update_vals env tr.tr_assigns sigma in
  let nv = update_arrs sigma env nv tr.tr_upds in
  let nv, lockq,cond_sets, semaphores = update_locks_unlocks sigma env nv tr lock_queue cond_sets semaphores in 
  upd_non_dets nv tr.tr_nondets,lockq,cond_sets, semaphores
    
    
let apply_transition args trname trans (env,lock_queue,cond_sets, semaphores) =
  let tr = Trans.find trname trans in
  let tr_args = List.map fst tr.tr_args in (* MODIFIED subsorts*)

  let arg_length = List.length tr.tr_args in
  if List.length args <> arg_length then
    raise (TopError (WrongArgs (trname,arg_length)));
  let sigma = Variable.build_subst tr_args args in 
  check_actor_suspension sigma env tr.tr_process;
  check_subtype sigma env tr.tr_args;
  let new_env = check_reqs tr.tr_reqs env sigma trname in
  let procs = Variable.give_procs (Options.get_interpret_procs ()) in
  let trargs = List.map (fun x -> Variable.subst sigma x) tr_args in
  let ureqs = uguard sigma procs trargs tr.tr_ureq in
  (*List.iter (fun u -> Format.eprintf "checkingg : %a@." SAtom.print u) ureqs;*)
  (*Ureqs that have ORs are lists with multiple elements : no or means 1 el in list
    so instead of iter, it has to be a function because one of the elements has to satisfy 
  *)
  (*let () = List.iter (fun u -> check_reqs u env sigma trname) ureqs in*)

  let new_env = check_ureqs ureqs new_env sigma trname in
  let nv = update_vals new_env tr.tr_assigns sigma in
  let nv = update_arrs sigma new_env nv tr.tr_upds in
  let nv, lockq,cond_sets, semaphores = update_locks_unlocks sigma new_env nv tr lock_queue cond_sets semaphores in
  upd_non_dets nv tr.tr_nondets,lockq,cond_sets, semaphores


let explain_reqs reqs env sigma tname args=
  SAtom.fold (fun atom acc ->
    match atom with
      | Comp (t1,op,t2) ->
	if Options.debug_interpreter then 
	  Format.eprintf "Checking explain requirements, comparing t1 and t2: %a -- %a@." Term.print t1 Term.print t2;
	let b = check_comp t1 t2 env sigma op in
	if b then acc
	else SAtom.add (Comp(Term.subst sigma t1, op, Term.subst sigma t2)) acc	
      | True -> acc
      | False ->  SAtom.add atom acc 
      | Ite _ -> assert false
  ) reqs SAtom.empty

(*TODO: fix ureq explanation*) 
let explain args trname trans (env,lock_queue,cond_sets, semaphores) =
  let tr = Trans.find trname trans in
  let arg_length = List.length tr.tr_args in
  if List.length args <> arg_length then
    raise (TopError (WrongArgs (trname,arg_length)));
  let tr_args = List.map fst tr.tr_args in (* MODIFIED subsorts*)

  let sigma = Variable.build_subst tr_args args in
  try
    check_actor_suspension sigma env tr.tr_process;
    check_subtype sigma env tr.tr_args;

    let satom = explain_reqs tr.tr_reqs env sigma trname args in
    let procs = Variable.give_procs (Options.get_interpret_procs ()) in
    let trargs = List.map (fun x -> Variable.subst sigma x) tr_args in
    let ureqs = uguard sigma procs trargs tr.tr_ureq in
    let final =
      List.fold_left (fun acc u ->
	let r = explain_reqs u env sigma trname args in
      SAtom.union r acc ) satom ureqs
    in
    if SAtom.is_empty final then
      Format.printf "Transition %a(%a) NOT blocked@." Hstring.print trname Variable.print_vars args
    else
      begin
	Format.printf "Transition %a(%a) blocked because following reqs are false:@." Hstring.print trname Variable.print_vars args; 
	SAtom.iter (fun atom ->
      Format.printf "\t%a@." Atom.print atom) final
      end
  with
    | TopError SuspendedProc pp -> Format.printf "Transition %a(%a) blocked due to suspended %a@." Hstring.print trname Variable.print_vars args Term.print pp
    | TopError SleepingProc pp -> Format.printf "Transition %a(%a) blocked due to sleeping %a@." Hstring.print trname Variable.print_vars args Term.print pp
       
      
let check_duplicates l =
  let h = Hashtbl.create( List.length l) in
  List.iter (fun x ->
    try
      let b = Hashtbl.find h x in
      if b then raise (TopError DupProcs)
    with Not_found ->  Hashtbl.add h x true
  ) l

let possible_for_proc (env,_,_,_) trans all_procs aproc =
  let glob = ref env in 
  Trans.fold (fun x el (acc_np, acc_p) ->
    let name = el.tr_name in 
    let args = List.map fst el.tr_args in (*MODIFED subsorts*)
    let num_args = List.length args in
    let tr_procs = all_arrange num_args all_procs in
    if tr_procs = [] then
      begin
	try 
	  let sigma = Variable.build_subst args [] in
	  check_actor_suspension sigma env (Some aproc);
	  check_subtype sigma env el.tr_args;
	  let new_env = check_reqs el.tr_reqs env sigma name in 
	  let trargs = List.map (fun x -> Variable.subst sigma x) args in
	  let ureqs = uguard  sigma all_procs trargs el.tr_ureq in
	  (*List.iter (fun u -> check_reqs u env sigma name) ureqs;*)
	  glob := check_ureqs ureqs new_env sigma name; 
	  ((el,[])::acc_np, acc_p)
	with
	  | TopError _ -> (acc_np, acc_p)
	  | Stdlib.Sys.Break ->
	     raise Exit
	  | s -> let e = Printexc.to_string s in Format.printf "%s @." e;
		 assert false
      end
    else
      begin
	List.fold_left (fun (acc_np1, acc_p1) procs ->
	  let sigma = Variable.build_subst args procs in
	  try  
	    let f =
	      check_actor_suspension_sched sigma env el.tr_process (Elem(aproc,Var)) 
		(*TODO for SUBTYPE*)
	    in
	    if f then 
	      begin
		check_subtype sigma env el.tr_args;

		let new_env = check_reqs el.tr_reqs env sigma name in   
	      let trargs = List.map (fun x -> Variable.subst sigma x) args in
	      let ureqs = uguard  sigma all_procs trargs el.tr_ureq in
	      (*List.iter (fun u -> check_reqs u env sigma name) ureqs;*)
	      glob := check_ureqs ureqs new_env sigma name; 
	      acc_np1,((el, procs)::acc_p1)
	    end
	    else (acc_np1,acc_p1)
	  with
	    | TopError _ -> (acc_np1,acc_p1)
	    | Sys.Break -> 
	       raise Exit
	    | s -> let e = Printexc.to_string s in Format.printf "%s@." e; assert false      
	) (acc_np, acc_p) tr_procs
      end 
  ) trans ([],[]), !glob

let init_unsafe all_procs unsafes = 
  List.fold_left(fun acc (_,args, satom) ->
    let num_args = List.length args in
    let u_procs = all_arrange num_args all_procs in
    if u_procs = [] then satom::acc
    else 
      begin
	List.fold_left (fun acc2 procs ->
	  let sigma = Variable.build_subst args procs in
	  let n_s = SAtom.subst sigma satom in
	  (*Format.eprintf "n_s is: %a@." SAtom.print n_s;*)
	  n_s::acc2
	) acc u_procs
      end
  ) [] unsafes


let random_possible_trans (env,_,_,_) trans all_procs flag =
  assert false

    
let all_possible_transitions (env,_,_,_) trans all_procs flag=
  let glob = ref env in 
  Trans.fold (fun x el acc ->
    let name = el.tr_name in 
    let args = List.map fst el.tr_args in (*MODIFIED subsorts*)
    let num_args = List.length args in
    let tr_procs = all_arrange num_args all_procs in
    if tr_procs = [] then
      begin
	try
	  let sigma = Variable.build_subst args [] in
	  check_actor_suspension sigma env el.tr_process;
	  check_subtype sigma env el.tr_args;
	  let new_env = check_reqs el.tr_reqs env sigma name in
	  let trargs = List.map (fun x -> Variable.subst sigma x) args in

	  let ureqs = uguard sigma all_procs trargs el.tr_ureq in
	  (*List.iter (fun u -> check_reqs u env sigma name) ureqs;*)
	  glob := check_ureqs ureqs new_env sigma name; 
	  (el,[])::acc
	with
	  | TopError _ -> acc
	  | Stdlib.Sys.Break | Exit ->
	    if ((Options.get_int_brab ()) <> -1) then raise Exit
	    else 
	    if flag 
	    then
	      raise (TopError StopExecution)
	    else raise Exit
	  | s -> let e = Printexc.to_string s in Format.printf "%s @." e;
		 acc
      end
    else
      begin
	List.fold_left (fun acc_t procs ->
	  let sigma = Variable.build_subst args procs in
	  try
	    check_actor_suspension sigma env el.tr_process;
	    check_subtype sigma env el.tr_args;

	    let new_env = check_reqs el.tr_reqs env sigma name in

	    let trargs = List.map (fun x -> Variable.subst sigma x) args in

	    let ureqs = uguard sigma all_procs trargs el.tr_ureq in

	    (*List.iter (fun u -> check_reqs u env sigma name) ureqs;*)
	    glob := check_ureqs ureqs new_env sigma name;
	    (el, procs)::acc_t
	  with
	    | TopError _ -> acc_t
	    | Sys.Break | Exit->
	      if ((Options.get_int_brab ()) <> -1) then raise Exit else 
	      if flag 
	      then
		raise (TopError StopExecution)
	      else raise Exit
	    | s ->(* let e = Printexc.to_string s in Format.printf "%s@." e; *)raise Exit    
	) acc tr_procs
      end 
  ) trans []

let env_to_satom env =
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


  
let weight_env (env,_,_,_) req env_old weight= 
  let potential = env_to_satom env in
  let old = env_to_satom env_old in 
  SAtom.fold (fun atom acc ->
    (*Format.eprintf "Trying: %a@." Atom.print atom;*)
    let f = 
    try
      let _ = SAtom.find atom potential
      in true
    with
      | Not_found -> false
    in
    let f_old =
      try
	let _ = SAtom.find atom old
	in true
      with
	| Not_found -> false
    in
    match f, f_old with
      | true, true -> acc + 1
      | true, false -> acc + 1
      | false, true -> acc - 1
      | false, false -> acc 	
  ) req weight



    
    
let all_possible_weighted_transitions global trans all_procs (env2,_,_,_) tr flag =
  let env, _,_,_ = global in
  (*let des_procs =  all_arrange (List.length tr.tr_args) all_procs in*)
  let glob = ref env in
  Trans.fold (fun x el acc ->
    let name = el.tr_name in 
    let args = List.map fst el.tr_args in (*MODIFIED subsorts*)
    let num_args = List.length args in
    let tr_procs = all_arrange num_args all_procs in
    if tr_procs = [] then
      begin
	try
	  let sigma = Variable.build_subst args [] in
	  check_actor_suspension sigma env el.tr_process;
	  check_subtype sigma env el.tr_args;

	  let new_env = check_reqs el.tr_reqs env sigma name in 
	  let trargs = List.map (fun x -> Variable.subst sigma x) args in
	  let ureqs = uguard  sigma all_procs trargs el.tr_ureq in
	  (*List.iter (fun u -> check_reqs u env sigma name) ureqs;*)
	  glob := check_ureqs ureqs new_env sigma name; 
	  let new_env = apply_transition [] name trans global in
	  let reqs = SAtom.subst sigma tr.tr_reqs in
	  if flag then
	    begin
	      let d = weight_env new_env reqs env2 0 in


	      (*let d =
		List.fold_left (fun acc1 el ->
		  let sigma' = Variable.build_subst tr.tr_args el in
		  let p = SAtom.subst sigma' tr.tr_reqs in 
		  (weight_env new_env p env 0) + acc1) 0 des_procs in *)

	      
	      let d1 =
		List.fold_left(fun acc satom ->
		  weight_env new_env satom env2 acc) 0 ureqs in
	      (d+d1,el,[])::acc
	    end 
	  else
	    (0,el,[])::acc

	with
	  | TopError _ -> acc
	  | Stdlib.Sys.Break ->
	     raise Exit
	  | s -> let e = Printexc.to_string s in Format.printf "%s @." e;
		 assert false
      end
    else
      begin
	List.fold_left (fun acc_t procs ->
	  let sigma = Variable.build_subst args procs in
	  try
	    check_actor_suspension sigma env el.tr_process;
	    check_subtype sigma env el.tr_args;

	    let new_env = check_reqs el.tr_reqs env sigma name in 
	    let trargs = List.map (fun x -> Variable.subst sigma x) args in
	    let ureqs = uguard  sigma all_procs trargs el.tr_ureq in
	    (*List.iter (fun u -> check_reqs u env sigma name) ureqs;*)
	    glob := check_ureqs ureqs new_env sigma name;  (*TODO: DOUBLE CHECK*)
	    let new_env = apply_transition procs name trans global in
	    let reqs = SAtom.subst sigma tr.tr_reqs in
	    let nureqs = uguard sigma all_procs trargs tr.tr_ureq in (*ureqs for desired*)
	    if flag then
	      begin
		let d = weight_env new_env reqs env2 0 in
		(*let d =
		List.fold_left (fun acc1 el ->
		  let sigma' = Variable.build_subst tr.tr_args el in
		  let p = SAtom.subst sigma' tr.tr_reqs in 
		  (weight_env new_env p env 0) + acc1) 0 des_procs in *)
		let d1 =
		  List.fold_left(fun acc satom ->
		    weight_env new_env satom env2 acc) 0 nureqs in
		(d+d1,el, procs)::acc_t
	      end
	    else (0,el, procs)::acc_t
	  with
	    | TopError _ -> acc_t
	    | Sys.Break -> 
	      raise Exit
	    | s -> let e = Printexc.to_string s in Format.printf "%s@." e; assert false      
	) acc tr_procs
      end 
  ) trans []


let entropy_env env trans allprocs =
  
  let poss = all_possible_transitions env trans allprocs false in
  let poss_num = float (List.length poss) in
  if poss_num = 0. then 0. else
    Float.log2 poss_num
  
(*let prob = 1. /. poss_num in *)
(*
  entropy = - SUM Pi*(log2 1/Pi) 
  since all of our Pi's are equal, this becomes:
  prob*(log2 1/prob) * poss
  => log2 poss_num
*)

    
let biased_entropy_env env trans allprocs probability =
  let poss = all_possible_transitions env trans allprocs false in

  let sum =
    List.fold_left (fun acc (el,_) -> let p = List.assoc el.tr_name probability in
				acc +. (p *. Float.log2 p)) 0.0 poss 
      
  in -. sum 

  

  
