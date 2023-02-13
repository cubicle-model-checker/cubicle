open Ast
open Types

type top_error =
  | InputError
  | NoTransition of Hstring.t
  | WrongArgs of Hstring.t * int
  | NoVar of Hstring.t
  | TooManyProcs
  | FalseReq of Hstring.t
  | ConflictInit of Hstring.t * Hstring.t
  | UnEqConstr of Hstring.t * Hstring.t
  | CannotProc
  | DupProcs
  | Unsafe
  | Reached
  | BadType of Hstring.t * Hstring.t
  | BadInit
  | SuspendedProc of Term.t
  | SleepingProc of Term.t 
  | CantUnlockOther of Term.t * Term.t
  | CantWaitNeverLock of Term.t * Term.t
  | UnlockedNotify
  | CantNotifyNotMine of Term.t * Term.t
  | Deadlock
  | StopExecution
  | StepNotMod of int
  | AbsentStep of int
  | StepTooBig of int * int
  | CannotBacktrack of int
  | ExplainReq of Hstring.t * Hstring.t list * Atom.t 

      

type q = (int * Hstring.t * Variable.t list * int * int) Interpret_types.PersistentQueue.t
type e = (Interpret_types.interpret_value Interpret_types.Env.t *
 Types.Term.t Interpret_types.PersistentQueue.t Interpret_types.LockQueues.t *
 Types.Term.t list Interpret_types.Conditions.t *
 Interpret_types.Env.key list Interpret_types.Semaphores.t)

      
type run_error =
  | ReachedUnsafe of q * e 
  | Deadlocked of q * e 
  | ReachedSteps of q * e
  | FinishedRun of q * e 
     
exception TopError of top_error
exception RunError of run_error


val top_report : Format.formatter -> top_error -> unit

val top_error : top_error -> 'a
