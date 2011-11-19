(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Options
open Format
open Solver
open Solver_types

type gformula = { 
  f:Formula.t; 
  age: int; 
  name: Formula.t option; 
  mf: bool;
  gf: bool;
}

type t = unit

exception Sat of t 
exception Unsat of Explanation.t
exception I_dont_know

let empty = ()

let steps = ref 0L
let start () = steps := 0L
let stop () = !steps
let pred_def _ = assert false


let print_stats () = 
  if Debug1.d_decisions  then begin
    let cpu_time = TimerSat.get() in
    eprintf "===============================================================================@.";
    
    eprintf "restarts              : %-12l@." env.starts;
    
    eprintf "conflicts             : %-12l   (%.0f /sec)@."
      env.conflicts ((to_float env.conflicts) /. cpu_time);
    
    eprintf "decisions             : %-12l   (%.0f /sec)@."
      env.decisions ((to_float env.decisions) /. cpu_time);
    
    eprintf "propagations          : %-12l   (%.0f /sec)@."
      env.propagations ((to_float env.propagations) /. cpu_time);
    
    eprintf "conflict literals     : %-12l   (%4.2f %% deleted)@."
      env.tot_literals 
      ((to_float (env.max_literals - env.tot_literals)) *. 100. /. 
         (to_float env.max_literals));
    
    eprintf "CPU time              : %g s@." cpu_time
  end
      
(*let _ = at_exit print_stats*)

(***


let main = 

***)


let check () =
  try solve ()
  with 
    | Solver.Sat -> ()
    | Solver.Unsat ->
      raise (Unsat Explanation.empty)


let assume gf = 
  let f = Formula.simplify gf.f in
  let cnf = Formula.cnf f in
  try assume_cnf cnf
  with Solver.Unsat -> raise (Unsat Explanation.empty)

let unsat env gf = 
    assume gf;
    check ();
    raise (Sat ())

let clear () = Solver.clear ()
