open Interpret_types
open Interpret_errors
open Types

(*
Scenario controller:
- which transitions must follow which transitions, ex:
between t1 and t1 must t2
between t1 and t2 must t3 
between t1 and t2 never t2 
never t1[2]
never t1 t2 t3 
every 5 steps t1 

- hold back procs 
always choose #1 
never choose #1 

- transition choice:
always choose t1 
never choose t2 
prefer t1 if total steps > 10  
*)
