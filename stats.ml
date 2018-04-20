(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
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
open Types

exception ReachedLimit


let round = 
  if not (profiling  && verbose > 0) then fun _ -> () 
  else fun cpt -> eprintf "@.-- Round %d@." cpt

let cpt_fix = ref 0

let cpt_nodes = ref 0

let cpt_process = ref 0

let cpt_restart = ref 0

let cpt_delete = ref 0

let nodes_pre_run = ref []

let new_node s =
  incr cpt_nodes;
  cpt_process := max !cpt_process (List.length (Node.variables s));
  if not quiet then
    begin
      printf "node @{<b>%d@}: " !cpt_nodes;
      if verbose < 1 then printf "@[%a@]@." Node.print_history s
      else printf "@[%a@] =@\n     @[%a@]@." Node.print_history s Node.print s
    end;
  if dot then Dot.new_node s

let check_limit s =
  if !cpt_nodes > maxnodes || s.depth > maxrounds then raise ReachedLimit
      
let fixpoint s uc =
  incr cpt_fix;
  if dot then Dot.fixpoint s uc

let restart () =
  incr cpt_restart;
  if not quiet then
    printf "%a@{<b>@{<fg_yellow>BACKTRACKING@} : %d restarts ...@}\n%a@."
           Pretty.print_line () !cpt_restart Pretty.print_line ();
  nodes_pre_run := !cpt_nodes :: !nodes_pre_run;
  cpt_nodes := 0;
  if dot then Dot.restart ()

let rec int_list_sep sep fmt = function
  | [] -> ()
  | [x] -> fprintf fmt "%d" x
  | x :: r -> fprintf fmt "%d%s%a" x sep (int_list_sep sep) r

let print_rounds_nb fmt () =
  if not quiet && !nodes_pre_run <> [] then
    fprintf fmt "@ (nodes %a)" (int_list_sep " + ") !nodes_pre_run


let candidate n c =
  if not quiet then
    begin
      printf "└───>> Approximating by @{<fg_blue>[%d]@}@." c.tag;
      if true || verbose > 0 then
        printf  "                        @[%a@]@." Node.print c
    end;
  if dot then Dot.candidate n c
      

let delete nb =
  cpt_delete := nb + !cpt_delete

let remaining compute = 
  if not quiet then
    let r, post = compute () in
    if post_strategy = 0 then
      printf "%s@{<dim>%d remaining@}\n@."
             (String.make (Pretty.vt_width - 10 - nb_digits r) ' ') r
    else
      let tot = r + post in
      printf "%s@{<dim>%d (%d+%d) remaining@}\n@."
             (String.make (Pretty.vt_width - 14 - (nb_digits r) - 
                             (nb_digits post) - (nb_digits tot)) ' ')
        tot r post


let print_candidates ~safe candidates =
  if candidates <> [] then
    begin
      let candidates = List.fast_sort Node.compare_by_breadth candidates in
      if safe then 
        Pretty.print_title std_formatter "INFERRED NEGATED INVARIANTS"
      else
        Pretty.print_title std_formatter "USED CANDIDATES";
      let cpt = ref 0 in
      List.iter (fun c ->
                 incr cpt;
                 printf "(%d)  %a@." !cpt
                        SAtom.print_inline (Node.litterals c))
                candidates;
    end


let print_trace faulty fmt trace =
  let o = Node.origin faulty in
  let first = ref true in
  List.iter 
    (fun (before, tr, sigma, after) ->
       if !first then begin
         fprintf fmt "@[<hov4>(Init) ->";
         if verbose > 0 then fprintf fmt "@ %a" SAtom.print before;
         fprintf fmt "@ @]@,";
       end;
       first := false;
       fprintf fmt "@[<hov4>%a(%a) ->"
         Hstring.print tr.tr_name Variable.print_vars (List.map snd sigma);
       if verbose > 0 then fprintf fmt "@ %a" SAtom.print after;
       fprintf fmt "@ @]@,";
    ) trace;
  if o.kind = Approx then fprintf fmt "@{<fg_blue>approx[%d]@}" o.tag
  else fprintf fmt "@{<fg_magenta>unsafe[%d]@}" o.tag

let print_trace faulty fmt trace =
  let o = Node.origin faulty in
  let first = ref true in
  List.iter 
    (fun (before, tr, sigma, after) ->
       if !first then begin
         fprintf fmt "@[<hov4>Init ->";
         if verbose > 0 then fprintf fmt "@ %a" SAtom.print before;
         fprintf fmt "@ @]@,";
       end;
       first := false;
       fprintf fmt "@[<hov4>%a(%a) ->"
         Hstring.print tr.tr_name Variable.print_vars (List.map snd sigma);
       if verbose > 0 then fprintf fmt "@ %a" SAtom.print after;
       fprintf fmt "@ @]@,";
    ) trace;
  if o.kind = Approx then fprintf fmt "@{<fg_blue>approx[%d]@}" o.tag
  else fprintf fmt "@{<fg_magenta>unsafe[%d]@}" o.tag

let print_history fmt n =
  fprintf fmt "@[<hov4>Init ->";
  if verbose > 0 then fprintf fmt "@ %a" Node.print n;
  fprintf fmt "@ @]@,";
  let last = List.fold_left 
      (fun last (tr, args, a) ->
         fprintf fmt "@[<hov4>%a(%a) ->"
           Hstring.print tr.tr_name Variable.print_vars args;
         if verbose > 0 then fprintf fmt "@ %a" Node.print a;
         fprintf fmt "@ @]@,";
      a
    ) n n.from in
  if last.kind = Approx then fprintf fmt "@{<fg_blue>approx[%d]@}" last.tag
  else fprintf fmt "@{<fg_magenta>unsafe[%d]@}" last.tag 


let error_trace sys faulty =
  if not quiet then
    match Forward.replay_history sys faulty with
    | None ->
      printf "@\n@{<fg_red>Spurious trace@}\n@.";
      raise Exit
    | Some trace ->
      printf "@\n@{<fg_red>Error trace@}: ";
      (* printf "@[%a@]@." (print_trace faulty) trace *)
      printf "@[%a@]@." print_history faulty


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

let print_time_simpl () =
  printf "├─Time for simplifications       : %a@." print_time (TimeSimpl.get ())

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

let print_time_ccheck () =
  printf "Filter candidates                : %a@." print_time (TimeCheckCand.get ())

let print_time_forward () =
  printf "Forward exploration              : %a@." print_time (TimeForward.get ())

let print_time_safety () =
  printf "Time for safety                  : %a@." print_time (TimeSafety.get ())

let print_time_satrc () =
  printf "Satisfying recvs with sends      : %a@." print_time (TimeSatRecv.get ())

let print_time_buildrs () =
  printf "├─Computing recv-send pairs      : %a@." print_time (TimeBuildRS.get ())

let print_time_filterrs () =
  printf "├─Filtering recv-send pairs      : %a@." print_time (TimeFilterRS.get ())

let print_report ~safe visited candidates =
  print_candidates ~safe candidates;
  Pretty.print_title std_formatter "STATS";
  printf "Number of visited nodes          : %d@." !cpt_nodes;
  printf "Fixpoints                        : %d@." !cpt_fix;
  printf "Number of solver calls           : %d@." (Prover.SMT.get_calls ());
  printf "Max Number of processes          : %d@." !cpt_process;
  if Options.delete then 
    printf "Number of deleted nodes          : %d@." !cpt_delete;
  if do_brab then
    printf "Number of %s             : %d@."
           (if safe then "invariants" else "candidates") (List.length candidates);
  printf "Restarts                         : @[%d%a@]@." !cpt_restart
         print_rounds_nb ();
  if profiling then
    begin
      printf "%a" Pretty.print_line ();
      print_time_pre ();
      print_time_fix ();
      print_time_rp ();
      print_time_simpl ();
      print_time_subset ();
      print_time_apply ();
      print_time_sort ();
      print_time_formulas ();
      print_time_prover ();
      print_time_forward ();
      print_time_ccheck ();
      print_time_safety ();
      print_time_satrc ();
      print_time_buildrs ();
      print_time_filterrs ()
    end;
  printf "%a" Pretty.print_double_line ()


let print_file_size fmt n =
  let nf = ref (float_of_int n) in
  if !nf < 1024. then fprintf fmt "%.1f B" !nf
  else begin
      nf := !nf /. 1024.;
      if !nf < 1024. then fprintf fmt "%.1f kB" !nf
      else begin
          nf := !nf /. 1024.;
          if !nf < 1024. then fprintf fmt "%.1f MB" !nf
          else begin
              nf := !nf /. 1024.;
              fprintf fmt "%.1f GB" !nf
            end
        end
    end
         
         
let print_time_certificate () =
  printf "Certificate generation : %a@." print_time (TimeCertificate.get ())

let print_stats_certificate visited cname =
  printf "Certificate generation : %a@." print_time (TimeCertificate.get ());
  printf "Quantified clauses : %d@." (List.length visited);
  printf "File size : %a@." print_file_size (Unix.stat cname).Unix.st_size
  
