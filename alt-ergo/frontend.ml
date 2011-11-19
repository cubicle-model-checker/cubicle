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

open Why_ptree

let _ = 
  Sys.set_signal Sys.sigint 
    (Sys.Signal_handle 
       (fun _ -> print_endline "User wants me to stop."; exit 1))

open Lexing
open Format
open Options

module Time = struct

  open Unix
    
  let u = ref 0.0
    
  let start () = u:=(times()).tms_utime

  let get () = 
    let res = (times()).tms_utime -. !u in
    start();
    res

end

type output = Unsat of Explanation.t | Inconsistent | Sat | Unknown

let check_produced_proof dep = ()
  (* if verbose then  *)
  (*   fprintf fmt "checking the proof:\n-------------------\n%a@."  *)
  (*     Explanation.print_proof dep; *)

  (* try *)
  (*   let env = *)
  (*     (Formula.Set.fold *)
  (*        (fun f env ->  *)
  (*           Sat.assume env {Sat.f=f;age=0;name=None;mf=false;gf=false} *)
  (*        ) (Explanation.formulas_of dep) Sat.empty) *)
  (*   in *)
  (*   raise (Sat.Sat env) *)
  (* with  *)
  (*   | Sat.Unsat _  -> () *)
  (*   | (Sat.Sat _ | Sat.I_dont_know) as e -> raise e *)


let process_decl print_status (env, consistent, dep) d =
  try
    match d.st_decl with
      | Assume(f,mf) -> 
	  Sat.assume {Sat.f=f;age=0;name=None;mf=mf;gf=false},
	  consistent, dep

      |	PredDef f -> 
	Sat.pred_def env f , consistent, dep

      | RwtDef r -> assert false

      | Query(n, f, lits)-> 
	  let dep = 
	    if consistent then
	      let dep' = Sat.unsat env 
		{Sat.f=f;age=0;name=None;mf=true;gf=true} in
	      Explanation.union dep' dep
	    else dep
          in
          if debug_proof then check_produced_proof dep;
	  print_status d (Unsat dep) (Sat.stop ());
	  env, consistent, dep
  with 
    | Sat.Sat _ -> 
	print_status d Sat (Sat.stop ());
	env , consistent, dep
    | Sat.Unsat dep' -> 
        let dep = Explanation.union dep dep' in
        if debug_proof then check_produced_proof dep;
	print_status d Inconsistent (Sat.stop ());
	env , false, dep
    | Sat.I_dont_know -> 
	print_status d Unknown (Sat.stop ());
	env , consistent, dep

let get_smt_prelude () =
  let libdir =
    try Sys.getenv "ERGOLIB"
    with Not_found -> Version.libdir
  in
  let f = Filename.concat libdir "smt_prelude.mlw"
  in
  from_channel (open_in f)

let open_file file lb =
  let d ,status =
    if !smtfile then begin
      let _ = get_smt_prelude () in 
      (*let lp = Why_parser.file Why_lexer.token lb_prelude in*)
      let bname,l,status = Smt_parser.benchmark Smt_lex.token lb in
      if verbose then printf "converting smt file : ";
      let l = List.flatten (List.map Smt_to_why.bench_to_why l) in
      if verbose then printf "done.@.";
      if parse_only then exit 0;
      let ltd = Why_typing.file (l) in
      let lltd = Why_typing.split_goals ltd in
      lltd, status
    end
    else if !smt2file then begin
      let commands = Smtlib2_parse.main Smtlib2_lex.token lb in
      if verbose then printf "converting smt2 file : ";
      let l = Smtlib2_to_why.smt2_to_why commands in
      if verbose then printf "done.@.";
      if parse_only then exit 0;
      let ltd = Why_typing.file l in
      let lltd = Why_typing.split_goals ltd in
      lltd, Smt_ast.Unknown
    end
    else
      let a = Why_parser.file Why_lexer.token lb in
      if parse_only then exit 0;
      let ltd = Why_typing.file a in
      let lltd = Why_typing.split_goals ltd in
      lltd, Smt_ast.Unknown
  in
  if file <> " stdin" then close_in cin;
  if type_only then exit 0;
  d, status

let pruning = 
  List.map
    (fun d -> 
       if select > 0 then Pruning.split_and_prune select d 
       else [List.map (fun f -> f,true) d])
    
let processing report declss = 
  Sat.start ();
  let declss = List.map (List.map fst) declss in
  List.iter
    (List.iter 
       (fun dcl ->
	  let cnf = Cnf.make dcl in 
	  ignore (Queue.fold (process_decl report)
		    (Sat.empty, true, Explanation.empty) cnf)
       )) (pruning declss)
