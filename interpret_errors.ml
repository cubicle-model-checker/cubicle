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

    
let top_report fmt e =
  match e with
    | InputError -> Format.fprintf fmt "Interpreter error: unknown input"
    | NoTransition err -> Format.fprintf fmt "Interpreter error: No transition called %a" Hstring.print err
    | WrongArgs(n,a1) -> Format.fprintf fmt "Interpreter error: transition %a requires %d argument(s)." Hstring.print n a1
    | NoVar v -> Format.fprintf fmt "Interpreter error: variable %a does not exist" Hstring.print v
    | TooManyProcs -> Format.fprintf fmt "Interpreter error: Please limit number of procs to <= 11"
    | FalseReq t -> Format.fprintf fmt "Requirements for transition %a are not satisfied" Hstring.print t
    | ConflictInit (n1,n2) ->
      Format.fprintf fmt "Conflicting definitions for %a and %a in init" Hstring.print n1 Hstring.print n2
    | UnEqConstr(n1, n2) ->
      Format.fprintf fmt "Constructors  %a and %a are not equal" Hstring.print n1 Hstring.print n2
    | CannotProc ->  Format.fprintf fmt "Cannot compare procs in init"
    | DupProcs -> Format.fprintf fmt "Transition arguments must be unique procs"
    | Reached -> ()
    | Unsafe -> Format.fprintf fmt "@{<b>@{<fg_red>WARNING@}@}: Current state is unsafe"
    | BadType(t1, t2) ->
      Format.fprintf fmt "Assignment error: types %a and %a are not compatible" Hstring.print t1 Hstring.print t2
    | BadInit ->
      Format.fprintf fmt "Bad initial state"
    | SuspendedProc t -> Format.fprintf fmt "Error: Process %a is suspended" Term.print t
    | SleepingProc t -> Format.fprintf fmt "Error: Process %a is asleep" Term.print t
    | CantUnlockOther(t1,t2) ->
      Format.fprintf fmt "Process %a cannot unlock %a's lock" Term.print t1 Term.print t2
    | CantWaitNeverLock(p, l) ->
      Format.fprintf fmt "Process %a cannot wait since it has never previously acquired %a@." Term.print p Term.print l
    | UnlockedNotify -> Format.fprintf fmt "Cannot notify with unlocked lock"
    | CantNotifyNotMine(proc,l) -> Format.fprintf fmt "Process %a can't notify: lock %a does not belong to %a@." Term.print proc Term.print l Term.print proc
    | Deadlock -> Format.fprintf fmt "@{<b>@{<fg_red>WARNING: Deadlock reached@}@}"
    | StopExecution -> Format.fprintf fmt "Execution interrupted"
    | StepNotMod i ->
      Format.fprintf fmt "Cannot rerun trace from Step %d [Step %d is not registered]" i i
    | AbsentStep i ->
      Format.fprintf fmt "Step %d is absent from backtracking env [Step %d is not registered]" i i
    | StepTooBig (i,s)->
      Format.fprintf fmt "Step %d is not part of the trace [max %d steps taken]" i s
    | CannotBacktrack i ->
      Format.fprintf fmt "Cannot backtrack: state at Step %d is not saved" i

    | ExplainReq(tn, args, atom) ->
      Format.fprintf fmt "Transition %a(%a) blocked due to %a" Hstring.print tn Variable.print_vars args Atom.print atom
      
let top_error e = raise (TopError e)
