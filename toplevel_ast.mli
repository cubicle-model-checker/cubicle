open Types
  
type top_proc =
  | NormalProc of Hstring.t
  | ExecutingProc of Hstring.t


type toplevel =
  | TopTransition of (Hstring.t * Hstring.t list) list
  | TopShowEnv
  | TopPrintSys
  | TopAssign of Hstring.t * term * term
  | TopHelp
  | TopClear
  | TopAll
  | TopFuzz of int
  | TopRestart
  | TopUnsafe
  | TopGenProc
  | TopDump
  | TopRandom
  | TopExec
  | TopExecRetry of int * int
  | TopCount of int * int 
  | TopBacktrack of int
  | TopFlag of int
  | TopShowTrace
  | TopReplayTrace
  | TopGoto of int
  | TopRerun of int*int
  | TopCurrentTrace
  | TopWhy of Hstring.t * Hstring.t list
  | TopDebugHelp
  | TopDebugOff
  | TopPre of Hstring.t * Hstring.t list

  | TopExperiment of Hstring.t * int * float
