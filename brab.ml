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


let non_cfm_literals = ref SA.empty

let contains_non_cfm s = not (SA.is_empty (SA.inter s !non_cfm_literals))
let lit_non_cfm a = SA.mem a !non_cfm_literals


let remove_non_cfm_cand =
  List.filter (fun ({t_unsafe = _, c} as sc) ->
	       if contains_non_cfm c then false 
	       else (add_bad_candidate sc None; true))


let search_backtrack_brab search invariants procs uns =
  let candidates = ref [] in
  let rec search_rec uns =
    try
      search ~invariants ~visited:[] ~forward_nodes:[] ~candidates uns
    with
      | Search.Unsafe faulty ->
	  (* FIXME Bug when search is parallel *)
	  let o = origin faulty in
	  if not quiet then
            eprintf "The node %d = %a is UNSAFE@." o.t_nb Pretty.print_system o;
	  if o.t_nb >= 0 then raise (Search.Unsafe faulty);
          (* Restarting *)

          (* Enumerative.replay_trace_and_expand procs faulty; *)
          
          candidates := remove_cand o faulty !candidates uns;
          (* candidates := []; *)

	  (* Find out if bactrack is due to crash failure model,
             in which case record literals that do not respect CMF model *)
	  if Forward.spurious_due_to_cfm faulty then
	    begin
	      non_cfm_literals := 
		SAtom.union (snd o.t_unsafe) !non_cfm_literals;
              candidates := remove_non_cfm_cand !candidates;
	      eprintf "Non CFM literals = %a@." Pretty.print_cube !non_cfm_literals;
	    end;

          if verbose > 0 && not quiet then begin
            eprintf "%d used candidates :@." (List.length !candidates);
            List.iter (fun s ->
              eprintf "   %a\n@." Pretty.print_system s) !candidates;
            eprintf "%d bad candidates :@." (List.length !bad_candidates);
            List.iter (fun sa ->
              eprintf "   %a\n@." Pretty.print_cube sa) !bad_candidates;
          end;

          search_rec uns
  in
  search_rec uns


(**************************************************************)
(* Backward reachability with approximations and backtracking *)
(**************************************************************)
    
let brab search invariants uns =
  Oracle.init system;
  if only_forward then exit 0;
  search_backtrack_brab search invariants procs uns
