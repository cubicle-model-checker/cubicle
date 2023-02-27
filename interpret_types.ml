open Ast
open Types

let sys_procs = ref 0 


type conc_value =
  | VInt of int
  | VReal of float
  | VBool of bool
  | VConstr of Hstring.t
  | VProc of Hstring.t
  | VGlob of Hstring.t
  | VAccess of Hstring.t * Hstring.t list
  | VLock of bool * Term.t option
  | VRLock of bool * Term.t option * int
  | VSemaphore of int
  | VArith of Term.t 
  | VAlive | VSuspended | VSleep of int
  | UNDEF

type interpret_value = { value: conc_value; typ: Hstring.t}

let ty_int = Hstring.make "int"
let ty_real = Hstring.make "real"
let ty_bool = Hstring.make "bool"
let ty_proc = Hstring.make "proc"
let ty_lock = Hstring.make "lock"
let ty_rlock = Hstring.make "rlock"
let ty_condition = Hstring.make "condition"
let ty_semaphore = Hstring.make "semaphore"

let is_int h =
  Hstring.equal h ty_int

let is_real h =
  Hstring.equal h ty_real

let is_bool h =
  Hstring.equal h ty_bool

let is_proc h = 
  Hstring.equal h ty_proc

let is_lock h =
  Hstring.equal h ty_lock

let is_rlock h =
  Hstring.equal h ty_rlock

let is_condition h =
  Hstring.equal h ty_condition
    
let is_semaphore h =
  Hstring.equal h ty_semaphore


(*
module Environment = struct
  module E = Map.Make(struct type t = Types.Term.t let compare = Types.Term.compare end)
  module L = Map.Make(struct type t = Types.Term.t let compare=  Types.Term.compare end)
  module C = Map.Make(struct type t = Types.Term.t let compare=  Types.Term.compare end)
  module S = Map.Make(struct type t = Types.Term.t let compare=  Types.Term.compare end)

  let pp e = E.iter (fun k elem ->
    Format.printf "%a : %a@." Term.print k Term.print elem
  ) e
  let ppp () = ()
end*)

    
module Env = Map.Make(struct type t = Types.Term.t let compare = Types.Term.compare end)
module Trans = Map.Make(struct type t = Hstring.t let compare = Hstring.compare end)
module LockQueues = Map.Make(struct type t = Types.Term.t let compare=  Types.Term.compare end)
module Conditions = Map.Make(struct type t = Types.Term.t let compare=  Types.Term.compare end)
module Semaphores = Map.Make(struct type t = Types.Term.t let compare=  Types.Term.compare end)



  
module Backtrack = Map.Make(struct
  type t = int
  let compare = compare
end)

(*
module HT = Hashtbl.Make (Term)*)
(*
module Trace = struct
  type 'a t = 'a array

  let index = ref 0

  let length a = Array.length a

  let start i = index := i
  
end *)
  

module PersistentQueue = struct
  type 'a t = 'a list * 'a list

  let empty =
    ([], [])

  let is_empty = function
    | [], [] -> true
    | _ -> false

  let push x (o, i) =
    (o, x :: i)

  let pop = function
    | [], [] ->
        invalid_arg "pop"
    | x :: o, i ->
        x, (o, i)
    | [], i ->
      match List.rev i with
        | x :: o -> x, (o, [])
        | [] -> assert false

  let rec iter f = function
    | [], [] -> ()
    | x::o, i -> f x; iter f (o,i)
    | [], x::o -> f x; iter f ([],o)

  let rec fold f acc  = function
    | [], [] -> acc
    | x::o, i -> fold f (f acc x) (o,i)
    | [], x::o -> fold f (f acc x) ([],o)

end


type term_map = interpret_value Env.t
type lockq = Types.Term.t PersistentQueue.t LockQueues.t
type conds = Types.Term.t list Conditions.t
type semaphs = Types.Term.t list Semaphores.t

type global = term_map * lockq * conds * semaphs 


let print_val fmt v =
  match v with
    | VInt i -> Format.printf "%d" i
    | VReal r -> Format.printf "%f" r
    | VBool b -> Format.printf "%b" b
    | VConstr el | VGlob el  -> Format.printf "%a" Hstring.print el
    | VProc i -> Format.printf "%a" Hstring.print i
    | VLock(b, vo) ->
      if b then
	match vo with
	  | None -> assert false
	  | Some p -> Format.printf "locked by process %a" Term.print p
      else
	Format.printf "unlocked"
    | VAlive -> Format.printf "process active"
    | VSuspended -> Format.printf "process suspended"
    | VSleep _ -> Format.printf "process asleep"
    | VRLock (b,po,i) ->
      if b then
	 match po with
	   | None -> assert false
	   | Some p -> Format.printf "locked by process %a %d time(s)" Term.print p i
      else
	Format.printf "unlocked"
    | VSemaphore i -> Format.printf "%d" i
    | UNDEF -> Format.printf "%s" "UNDEF"
    | VAccess(l,t) -> Format.printf "%a[%a]" Hstring.print l (Hstring.print_list ", ") t
    | VArith _ -> ()


let print_interpret_val fmt {value=v; typ = t} =
  match v with
    | VInt i -> Format.printf "%d" i
    | VReal r -> Format.printf "%f" r
    | VBool b -> Format.printf "%b" b
    | VConstr el | VGlob el  -> Format.printf "%a" Hstring.print el
    | VProc i -> Format.printf "%a" Hstring.print i
    | VAccess(l,t) -> Format.printf "%a[%a]" Hstring.print l (Hstring.print_list ", ") t
    | VLock(b, vo) ->
      if b then
	match vo with
	  | None -> assert false
	  | Some p -> Format.printf "locked by process %a" Term.print p
      else
	Format.printf "unlocked"
    | VRLock _ -> ()
    | VAlive -> Format.printf "p
rocess active"
    | VSuspended -> Format.printf "process suspended"
    | VSleep _ -> Format.printf "process asleep"
    | VSemaphore i -> Format.printf "%d" i
    | UNDEF -> Format.printf "%s" "UNDEF"
    | VArith _ -> ()

let print_poss_trans fmt l =
  Format.printf "Possible transitions:@."; 
  List.iter (fun (t,p) -> Format.printf "transition %a(%a)@." Hstring.print t.tr_name Variable.print_vars p) l

let print_transition fmt tr args =
  Format.printf "transition %a(%a)" Hstring.print tr Variable.print_vars args

let print_applied_trans fmt l =
  Format.printf "Applied transitions:@.";
  let rec print_trans q =
    if PersistentQueue.is_empty q then ()
    else
      begin
	let (_,t,p,_,_),r = PersistentQueue.pop q in 
	Format.printf "\ttransition %a(%a)@." Hstring.print t Variable.print_vars p;
	print_trans r
      end 
  in print_trans l
  
let print_debug_trans_path fmt l i =
  Format.printf "Applied transitions:\n---\n  pre: possible transitions before\n  post: possible transitions after\n  MANUAL: transition applied manually, pre/post not calculated\n  @{<b>@{<fg_green>**Step <int>@}@}: resulting env stored and accessible\n---@.";
  if PersistentQueue.is_empty l then Format.printf "no applied transitions@.";
  let rec print_trans q =
    if PersistentQueue.is_empty q then ()
    else
      begin
	let (tn,t,p,ptpre, ptpost),r = PersistentQueue.pop q in
	let s1 =
	  if ptpre = -1 then "MANUAL"
	  else if ptpre = -2 then "-"
	  else string_of_int ptpre in
	let s2 =
	  if ptpost = -1 then "MANUAL"
	  else if ptpost = -2 then "-"
	  else string_of_int ptpost in
	
	if tn mod i = 0 then 
	  Format.printf "@{<b>@{<fg_green>**Step %d[pre: %s, post: %s]: transition %a(%a)@}@}@."
	    tn s1 s2 Hstring.print t Variable.print_vars p
	else
	  Format.printf "Step %d[pre: %s, post: %s]: transition %a(%a)@."
	    tn s1 s2 Hstring.print t Variable.print_vars p;
	print_trans r
      end 
  in print_trans l  
  

let print_title fmt s =
  Format.printf "@{<b>%s@}\n" s;
  Format.printf  "%a" Pretty.print_double_line ()
    
let print_env fmt env =
  print_title fmt "Environment";
  Env.iter(fun k elem ->
    Format.printf "%a : %a@." Term.print k Term.print elem
  ) env;
  Format.printf  "%a@." Pretty.print_line ()

let print_queue fmt el =
  let rec print_trans q =
    if PersistentQueue.is_empty q then ()
    else
      begin
	let x,r = PersistentQueue.pop q in 
	Format.printf "%a" Term.print x;
	print_trans r
      end 
  in print_trans el
  
  

let print_wait fmt el =
  List.iter (fun x -> Format.printf "%a " Term.print x) el


    
let print_interpret_env fmt (env,locks, cond, sem)=
  print_title fmt "Final Environment";
  Env.iter(fun k {value = v} ->
    Format.printf "%a : %a@." Term.print k print_val v
  ) env;
  Format.printf  "%a" Pretty.print_line ();
  Format.printf "Lock Queues:@.";
  LockQueues.iter (fun k el ->
    Format.printf "%a : { %a }@." Term.print k print_queue el) locks;
  Format.printf  "%a" Pretty.print_line ();
    Format.printf "Condition wait pools:@.";
  Conditions.iter (fun k el ->
    Format.printf "%a : { %a }@." Term.print k print_wait el) cond;
  Format.printf  "%a" Pretty.print_line ();
  Format.printf "Semaphore wait lists:@.";
  Semaphores.iter (fun k el ->
    Format.printf "%a : { %a }@." Term.print k print_wait el) sem;
  Format.printf  "%a" Pretty.print_line ()

let print_debug_env fmt (env,locks, cond, sem)=
  Env.iter(fun k {value = v} ->
    Format.printf "  %a : %a@." Term.print k print_val v
  ) env;
  Format.printf "  Lock Queues:@.";
  LockQueues.iter (fun k el ->
    Format.printf "   %a : { %a }@." Term.print k print_queue el) locks;
    Format.printf "  Condition wait pools:@.";
  Conditions.iter (fun k el ->
    Format.printf "   %a : { %a }@." Term.print k print_wait el) cond;
  Format.printf "  Semaphore wait lists:@.";
  Semaphores.iter (fun k el ->
    Format.printf "   %a : { %a }@." Term.print k print_wait el) sem;
  Format.printf  "%a" Pretty.print_line ()  

    
let print_help fmt =
  Format.printf
    "@{<b>@{<u>@{<fg_magenta_b>Usage:@}@}@}\n\
     Executing transitions:\n\
     \ttransition <name>(<args>) : apply a transition\n\
     \ttransition <name>(<args>); <name>(<args>)... : apply a sequence of transitions\n\n\
     @{<b>@{<u>@{<fg_magenta_b>Other Commands:@}@}@}\n\
     \thelp : display this list\n\
     \tstatus : show current environment\n\
     \texecute : run random execution\n\
     \texecute <N> <depth> : execute <depth> transitions <N> times. Looks for unsafe state\n\
     \tall : show possible transitions\n\
     \trandom : pick a random transition and apply it\n\
     \tunsafe : check if current state is unsafe\n\
     \treset : reset the environment [global system state, trace logs, backtracking info]\n\
     @{<b>@{<u>@{<fg_magenta_b>Debug Commands:@}@}@}\n\
     \tflag <int> : set how often debugger remembers states for easier backtracking\n\
     \ttrace  : show trace\n\
     \treplay : replay entire trace, waits for user OK after each step\n\
     \tbacktrack <int> : backtrack environment to Step <int>\n\
     \trerun <int> <int> : rerun trace between two steps, waits for user OK after each step\n\
     \twhy <transition call> : explain which values interfere with transition application\n\
     \tdhelp : show debug help@."


  
let print_debug_help fmt =
  Format.printf
    "@{<b>@{<u>@{<fg_magenta_b>Debug Commands:@}@}@}\n\
     \tflag <int> : set how often debugger remembers states for easier backtracking\n\
     \ttrace  : show trace\n\
     \treplay : replay entire trace, waits for user OK after each step\n\
     \tbacktrack <int> : backtrack environment to Step <int>\n\
     \trerun <int> <int> : rerun trace between two steps, waits for user OK after each step\n\
     \twhy <transition call> : explain which values interfere with transition application\n\
     \tdhelp : show debug help@."   


let str_op_comp = function Eq -> "=" | Lt -> "<" | Le -> "<=" | Neq -> "<>"

    
let int_of_const = function
  | ConstInt n -> Num.int_of_num n
  | ConstReal n -> Num.int_of_num (Num.integer_num n)
  | ConstName _ -> 1

let int_of_consts cs =
  MConst.fold (fun c i acc -> i * (int_of_const c) + acc) cs 0

let cub_to_val cv =
  match cv with
    | Elem(el, Glob) -> VGlob el
    | Elem(el, Var) -> VProc el
    | Elem(el, Constr) -> VConstr el
    | Access(el, vl) -> VAccess(el,vl)
    | Arith(t, im) -> VArith cv
    | Const i -> let x = int_of_consts i in VInt x
    | Elem(_, SystemProcs) -> VInt !sys_procs
    | ProcManip([t], PlusOne) ->
      begin
	match t with
	  | Elem(n, Var) -> let ni = Variable.number n in
			    let ni = ni + 1 in
			    let ns = string_of_int ni in
			    let h = Hstring.make ("#"^ns) in
			    VProc h
	  | _ -> assert false
      end
    | ProcManip([t], MinusOne) ->
      begin
	match t with
	  | Elem(n, Var) -> let ni = Variable.number n in
			    let ni = ni - 1 in
			    let ns = string_of_int ni in
			    let h = Hstring.make ("#"^ns) in
			    VProc h
	  | _ -> assert false
      end
    | ProcManip([t1;t2], CompProcs) -> assert false
    | ProcManip _ -> assert false

					 
let val_to_cub cv =
  match cv with
    | VGlob el -> Elem(el, Glob)
    | VProc el -> Elem(el, Var)
    | VConstr el -> Elem(el, Constr)
    | VAccess(el,vl) -> Access(el, vl)
    | _ -> assert false
  

let random_value h =
  Random.self_init ();
  match is_int h, is_real h, is_bool h,
    is_proc h, is_lock h, is_rlock h, is_condition h, is_semaphore h
  with
    | true, false, false, false, false, false, false, false -> VInt (Random.int 10)
    | false, true, false, false, false, false, false, false -> VReal (Random.float 10.)
    | false, false, true, false, false, false, false, false -> let r = Random.int 12 in
				   if r mod 2 = 0 then VBool true
				   else VBool false
    | false, false, false, true,false, false, false, false -> let r = (Random.int 25) mod (Options.get_interpret_procs () )in
				   let s = "#"^(string_of_int (r+1)) in
				   VProc (Hstring.make s)
    | false, false, false, false,false, false, false, false -> 
      let constrs = Smt.Type.constructors h in
      let arr = Array.of_list constrs in
      let r = Random.int (List.length constrs -1) in
      let el = arr.(r) in
      VConstr(el)
    | false,false,false,false,true, false, false, false -> VLock (false, None)
    | false, false, false, false, false, true, false,false -> VRLock(false, None, 0)
    | false, false, false, false, false, false, true, false -> VLock (false, None)
    | false, false, false, false, false, false, false, true -> VSemaphore(3) 
    | _  -> assert false

let random_different_constr typ v =
  let _,t = Smt.Symbol.type_of typ in
  let constrs = Smt.Type.constructors t in
  List.fold_left(fun acc el -> if Hstring.compare v el = 0 then acc else el) v constrs


let compare_conc v1 v2 =
  match v1,v2 with
    | VInt i1, VInt i2 -> compare i1 i2
    | VReal r1, VReal r2 -> compare r1 r2
    | VBool b1, VBool b2 -> compare b1 b2
    | VConstr v1, VConstr v2 -> Hstring.compare v1 v2
    | VProc p1, VProc p2 -> Hstring.compare p1 p2
    | VReal _ , VInt _ -> assert false
    | VConstr _, VInt _ -> assert false
    | VGlob _, VInt _ -> assert false
    | VSemaphore s1, VSemaphore v2 -> compare s1 v2
    | VSemaphore s1, VInt i1 -> compare s1 i1
    | VInt i1, VSemaphore s1 -> compare i1 s1
    | VLock (b1, to1), VLock(b2, to2) ->
      let b3 = b1 && b2 in
      begin
	match to1, to2 with 
	  | None, None -> if b3 then 0 else -1 
	  | None, Some _ | Some _, None -> -1
	  | Some p1, Some p2 ->
	    let comp = Term.compare p1 p2 in
	    if b3 then comp
	    else -1 	    
      end
    | VAlive, VAlive -> 0
    | VAlive, (VSuspended| VSleep _) -> 1
    | (VSuspended| VSleep _), VAlive -> -1
    | VSuspended, VSuspended -> 0
    | VSuspended, VSleep _ -> -1
    | VSleep _, VSuspended -> 1
    | VSleep i1, VSleep i2 -> compare i1 i2
    | _ -> assert false		     
      
let compare_interp_val v1 v2 =
  compare_conc v1.value v2.value
    
let all_constr_terms () =
  List.rev_map (fun x -> Elem (x, Constr)) (Smt.Type.all_constructors ())
       
let to_interpret term = 
  match term with
    | Elem( el, Glob) -> let _, ty = Smt.Symbol.type_of el in {value = VGlob el; typ = ty }
    | Elem( el, Constr) ->
      let _, ty = Smt.Symbol.type_of el in {value = VConstr el; typ = ty }
    | Elem( el, Var) -> {value = VProc el; typ = ty_proc }
    | Access(el,vl) -> let _, ty = Smt.Symbol.type_of el in {value = VAccess (el,vl); typ = ty }
    | Const cs -> let x = int_of_consts cs in {value = VInt x; typ = ty_int}
    | Arith(t,cs) -> assert false
    | Elem(_, SystemProcs) -> {value = VInt !sys_procs; typ = Smt.Type.type_int}
    | ProcManip([t], PlusOne) ->
      begin
	match t with
	  | Elem(n, Var) -> let ni = Variable.number n in
			    let ni = ni + 1 in
			    let ns = string_of_int ni in
			    let h = Hstring.make ("#"^ns) in
			    {value = VProc h; typ = Smt.Type.type_proc}
	  | _ -> assert false
      end
    | ProcManip([t], MinusOne) ->
      begin
	match t with
	  | Elem(n, Var) -> let ni = Variable.number n in
			    let ni = ni - 1 in
			    let ns = string_of_int ni in
			    let h = Hstring.make ("#"^ns) in
			    {value = VProc h; typ = Smt.Type.type_proc}
	  | _ -> assert false
      end
    | ProcManip([t1;t2], CompProcs) -> assert false
    | ProcManip _ -> assert false

   
let interpret_comp b op =
  match op with
    | Eq -> b = 0
    | Lt -> b = -1
    | Le -> b = 0 || b = -1
    | Neq -> b <> 0 



let compare_queues q1 q2 =
  let rec aux q1 q2 =
    let b1 = PersistentQueue.is_empty q1 in
    let b2 = PersistentQueue.is_empty q2 in  
    match b1, b2 with
      | true, true -> 0
      | true, false -> -1
      | false, true -> 1
      | false, false ->
	let el1,rem1 = PersistentQueue.pop q1 in
	let el2, rem2 = PersistentQueue.pop q2 in
	let comp = Types.Term.compare el1 el2 in 
	if comp = 0 then
	  aux rem1 rem2
	else
	  comp
  in aux q1 q2

let compare_term_lists l1 l2 =
  let rec aux l1 l2 =
    match l1,l2 with
      | [],[] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | hd1::tl1,hd2::tl2 ->
	let comp = Types.Term.compare hd1 hd2 in
	if comp = 0 then aux tl1 tl2
	else comp
  in aux l1 l2

      
let print_debug_color_env fmt (env,locks, cond, sem) (env_old, locks_old, cond_old,sem_old)=
    Env.iter(fun k {value = v} ->
      let {value = el} = Env.find k env_old in
      if compare_conc v el = 0 then
	Format.printf "  %a : %a@." Term.print k print_val v
      else
	Format.printf "  @{<b>@{<fg_green>%a : %a@}@}@." Term.print k print_val v
    ) env;
  Format.printf "  Lock Queues:@.";
  LockQueues.iter (fun k el ->
    let elm = LockQueues.find k locks_old in
    if compare_queues el elm = 0  then
      Format.printf "   %a : { %a }@." Term.print k print_queue el
    else
      Format.printf "   @{<b>@{<fg_green>%a : { %a }@}@}@." Term.print k print_queue el
    ) locks;
    Format.printf "  Condition wait pools:@.";
    Conditions.iter (fun k el ->
      let elm = Conditions.find k cond_old in
      if compare_term_lists el elm = 0 then
	Format.printf "   %a : { %a }@." Term.print k print_wait el
      else
	Format.printf "   @{<b>@{<fg_green>%a : { %a }@}@}@." Term.print k print_wait el
    ) cond;
    Format.printf "  Semaphore wait lists:@.";
    Semaphores.iter (fun k el ->
      let elm = Semaphores.find k sem_old in
      if compare_term_lists el elm = 0 then
	Format.printf "   %a : { %a }@." Term.print k print_wait el
      else
	Format.printf "   @{<b>@{<fg_green>%a : { %a }@}@}@." Term.print k print_wait el
    ) sem;
    Format.printf  "%a" Pretty.print_line ()    


let print_backtrace_env fmt benv =
  Backtrack.iter (fun key (name, args, env) ->
    Format.printf "Step %d: transition %a with args: %a@."
      key Hstring.print name Variable.print_vars args) benv


type q = (int * Hstring.t * Variable.t list * int * int) PersistentQueue.t

type e = (interpret_value Env.t * Types.Term.t PersistentQueue.t LockQueues.t * Types.Term.t list Conditions.t * Env.key list Semaphores.t)

let procs_to_int_list pl =
  List.fold_left (fun acc x -> let s = Hstring.view x in
			       let s1 = String.split_on_char '#' s in
			       match s1 with
				 | [a;b] -> int_of_string b::acc
				 | _ -> assert false ) [] pl
				 
			       
			   
