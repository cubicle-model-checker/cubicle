open Ast
open Types
open Interpret_types

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
  | BadSubType of Term.t * Hstring.t


     

      
type run_error =
  | ReachedUnsafe of q * global
  | Deadlocked of q * global
  | ReachedSteps of q * global
  | FinishedRun of q * global
     
exception TopError of top_error
exception RunError of run_error


val top_report : Format.formatter -> top_error -> unit

val top_error : top_error -> 'a
