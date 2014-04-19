(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Util
open Ast
open Options

let round = 
  if not (profiling  && verbose > 0) then fun _ -> () 
  else fun cpt -> eprintf "@.-- Round %d@." cpt

let cpt_fix = ref 0
                  
let cpt_nodes = ref 0

let cpt_process = ref 0

let cpt_restart = ref (-1)

let nodes_pre_run = ref []

let new_node s =
  incr cpt_nodes;
  cpt_process := max !cpt_process (List.length (Node.variables s));
  if not quiet then
    begin
      printf "node @{<b>%d@}: " !cpt_nodes;
      if verbose < 1 then printf "@[%a@]@." Node.print_history s
      else printf "@[%a@] = \n---@[%a@]---@." Node.print_history s Node.print s
    end
      
let fixpoint s uc =
  incr cpt_fix

let restart () =
  incr cpt_restart;
  if not quiet then printf "\n@{<b>@{<fg_yellow>Backtracking@} ...@}\n@." ;
  nodes_pre_run := !cpt_nodes :: !nodes_pre_run;
  cpt_nodes := 0


let candidate c =
  if not quiet then
    begin
      printf "└───>> Approximating by @{<b>[%d]@}@." c.tag;
      if verbose > 0 then printf  "@[%a@]@." Node.print c
    end    
      

let remaining r =
  if not quiet then
    printf "%s@{<dim>%d remaining@}\n@."
           (String.make (Pretty.vt_width - 10 - nb_digits r) ' ')
           r
           
let print_visited = 
  if not (profiling && verbose > 0) then fun _ -> ()
  else fun nb -> eprintf "Number of visited nodes : %d@." nb

let print_states st pr = 
  if not profiling then ()
  else List.iter
         (eprintf "%a@." pr) st

let print = 
  if not (profiling  && verbose > 0) then fun _ _ _ -> ()
  else fun str d size -> 
       eprintf "[%s %d] Number of processes : %d@." str d size

let print2 str d size =
  eprintf "[%s %d] Number of processes : %d@." str d size

let print_time fmt sec =
  let minu = floor (sec /. 60.) in
  let extrasec = sec -. (minu *. 60.) in
  fprintf fmt "%dm%2.3fs" (int_of_float minu) extrasec
          

let print_time_fix () =
  printf "Time for fixpoint                : %a@." print_time (TimeFix.get ())

let print_time_rp () =
  printf "├─Time for relevant permutations : %a@." print_time (TimeRP.get ())

let print_time_formulas () =
  printf "├─Time in formulas               : %a@." print_time (TimeFormula.get ())

let print_time_prover () =
  let sec = Prover.SMT.get_time () in
  printf "└─Time in solver                 : %a@." print_time sec
         
let print_time_pre () =
  printf "Time for pre-image computation   : %a@." print_time (TimePre.get ())

let print_time_subset () =
  printf "├─Subset tests                   : %a@." print_time (TimerSubset.get ())

let print_time_apply () =
  printf "├─Apply substitutions            : %a@." print_time (TimerApply.get ())

let print_time_sort () =
  printf "├─Nodes sorting                  : %a@." print_time (TimeSort.get ())

let print_time_custom () =
  printf "Custom timer                     : %a@." print_time (TimeCustom.get ())

let print_time_forward () =
  printf "Forward exploration              : %a@." print_time (TimeForward.get ())

let print_report nb inv del used_cands print_system =
  if used_cands <> [] then begin
                          printf "\n---------------------\n";
                          printf "@{<b>Inferred invariants :@}\n";
                          printf "---------------------@.";
                          List.iter (fun i -> printf "\n%a@." print_system i) used_cands
                        end;
  printf "\n----------------------------------------------@.";
  printf "Number of visited nodes          : %d@." nb;
  printf "Fixpoints                        : %d@." !cpt_fix;
  printf "Number of solver calls           : %d@." (Prover.SMT.get_calls ());
  printf "Max Number of processes          : %d@." !cpt_process;
  if delete then 
    printf "Number of deleted nodes          : %d@." del;
  printf "Number of invariants             : %d@." (List.length used_cands);  
  printf "Restarts                         : %d@." !cpt_restart;
  printf "----------------------------------------------@.";
  if profiling then
    begin
      print_time_pre ();
      print_time_fix ();
      print_time_rp ();
      print_time_subset ();
      print_time_apply ();
      print_time_sort ();
      print_time_formulas ();
      print_time_prover ();
      print_time_forward ();
      print_time_custom ();
      printf "----------------------------------------------@."
    end
