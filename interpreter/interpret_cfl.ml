open Interpret_calc
open Interpret_types
open Interpret_errors
open Ast
open Types
open Util


let visited_states = ref []
let visit_count = ref 0
(*
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
    *)

    
