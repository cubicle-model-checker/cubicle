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

exception TopError of top_error

val top_report : Format.formatter -> top_error -> unit

val top_error : top_error -> 'a
