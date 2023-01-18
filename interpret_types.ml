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

type interpret_value = { value: conc_value; typ: Hstring.t }

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
    
module Env = Map.Make(struct type t = Types.Term.t let compare = Types.Term.compare end)
module Trans = Map.Make(struct type t = Hstring.t let compare = Hstring.compare end)
module LockQueues = Map.Make(struct type t = Types.Term.t let compare=  Types.Term.compare end)
module Conditions = Map.Make(struct type t = Types.Term.t let compare=  Types.Term.compare end)
module Semaphores = Map.Make(struct type t = Types.Term.t let compare=  Types.Term.compare end)


module HT = Hashtbl.Make (Term)



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

let print_applied_trans fmt l =
  Format.printf "Applied transitions:@.";
  Queue.iter (fun (t,p) -> Format.printf "transition %a(%a)@." Hstring.print t.tr_name Variable.print_vars p) l 

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
  Queue.iter (fun x -> Format.printf "%a " Term.print x) el

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
  
let print_help fmt =
  Format.printf "@{<b>@{<fg_blue>Commands@}@}@.";
  Format.printf "help : display list of commands@.";
  Format.printf "status : show environment@.";
  Format.printf "transition <name> <(args)> : apply a transition to procs in args@."


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
    | true, false, false, false,false, false, false, false -> VInt (Random.int 10)
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
