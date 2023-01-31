open Ast
open Types

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

val sys_procs: int ref
    
val int_of_const : Types.const -> int

val int_of_consts : int Types.MConst.t -> int

val cub_to_val : Types.term -> conc_value

val val_to_cub : conc_value -> Types.term

val ty_int : Hstring.t
val ty_real : Hstring.t
val ty_bool : Hstring.t
val ty_proc : Hstring.t 
val ty_lock : Hstring.t
val ty_rlock : Hstring.t
val ty_condition : Hstring.t
val ty_semaphore : Hstring.t

val is_int : Hstring.t -> bool
val is_real : Hstring.t -> bool
val is_bool : Hstring.t -> bool
val is_proc : Hstring.t -> bool
val is_lock : Hstring.t -> bool
val is_rlock : Hstring.t -> bool
val is_condition : Hstring.t -> bool
val is_semaphore : Hstring.t -> bool

module Env : Map.S with type key = Types.Term.t
module Trans : Map.S with type key = Hstring.t 
module LockQueues : Map.S with type key = Types.Term.t
module Conditions : Map.S with type key = Types.Term.t
module Semaphores : Map.S with type key = Types.Term.t
module Backtrack : Map.S with type key = int 

module HT : Hashtbl.S with type key = Types.Term.t

module PersistentQueue : sig 
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val push : 'a -> 'a t -> 'a t
  val pop : 'a t -> 'a * 'a t
end
  
val int_of_const : Types.const -> int

val int_of_consts : int Types.MConst.t -> int

val cub_to_val : Types.Term.t -> conc_value

val val_to_cub : conc_value -> Types.term

val random_value : Hstring.t -> conc_value 

val random_different_constr : Smt.Symbol.t -> Hstring.t -> Hstring.t

val compare_conc : conc_value -> conc_value -> int

val compare_interp_val : interpret_value -> interpret_value -> int

val all_constr_terms : unit -> Types.term list

val to_interpret : Types.term -> interpret_value

val str_op_comp : Types.op_comp -> string

val interpret_comp : int -> Types.op_comp -> bool 
  
val print_val : Format.formatter -> conc_value -> unit

val print_interpret_val : Format.formatter -> interpret_value -> unit

val print_poss_trans : Format.formatter -> (Ast.transition_info * Variable.t list) list -> unit

val print_applied_trans : Format.formatter -> (int * Hstring.t * Variable.t list * int * int) PersistentQueue.t -> unit

val print_debug_trans_path : Format.formatter -> (int * Hstring.t * Variable.t list * int * int) PersistentQueue.t -> int -> unit  

val print_title : Format.formatter -> string -> unit

val print_env : Format.formatter -> Types.Term.t Env.t -> unit

val print_queue : Format.formatter -> Types.Term.t PersistentQueue.t -> unit

val print_wait : Format.formatter -> Types.Term.t list -> unit

val print_interpret_env : Format.formatter -> interpret_value Env.t * Types.Term.t PersistentQueue.t LockQueues.t *
  Types.Term.t list Conditions.t * Types.Term.t list Semaphores.t -> unit

val print_debug_env : Format.formatter ->
  interpret_value Env.t * Types.Term.t PersistentQueue.t LockQueues.t *
  Types.Term.t list Conditions.t * Types.Term.t list Semaphores.t -> unit


val print_debug_color_env : Format.formatter ->
  interpret_value Env.t * Types.Term.t PersistentQueue.t LockQueues.t *
  Types.Term.t list Conditions.t * Types.Term.t list Semaphores.t ->
  interpret_value Env.t * Types.Term.t PersistentQueue.t LockQueues.t *
  Types.Term.t list Conditions.t * Types.Term.t list Semaphores.t -> unit 
  

val print_help : Format.formatter -> unit
val print_debug_help : Format.formatter -> unit
val print_transition : Format.formatter -> Hstring.t -> Variable.t list -> unit

val print_backtrace_env : Format.formatter -> (Hstring.t * Variable.t list * 'a) Backtrack.t -> unit
