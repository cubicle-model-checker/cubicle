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

let process_decl print_status dep d =
  try
    match d.st_decl with
      | Assume f -> 
	  Sat.assume {Sat.f=f; age=0; name=None; gf=false};
	  dep

      |	PredDef f -> 
	  assert false

      | Query(n, f, lits)-> 
	  let dep = 
	    let dep' = Sat.unsat {Sat.f=f; age=0; name=None; gf=true} in
	    Explanation.union dep' dep
          in
	  print_status d (Unsat dep) (Sat.stop ());
	  dep
  with 
    | Sat.Sat _ -> 
	print_status d Sat (Sat.stop ());
	dep
    | Sat.Unsat dep' -> 
        let dep = Explanation.union dep dep' in
	print_status d Inconsistent (Sat.stop ());
	raise (Sat.Unsat dep)
    | Sat.I_dont_know -> 
	print_status d Unknown (Sat.stop ());
	dep

let open_file file lb =
  let d =
    let a = Why_parser.file Why_lexer.token lb in
    if parse_only then exit 0;
    let ltd = Why_typing.file a in
    let lltd = Why_typing.split_goals ltd in
    lltd
  in
  if file <> " stdin" then close_in cin;
  if type_only then exit 0;
  d

let processing report declss = 
  Sat.start ();
  (List.iter 
     (fun dcl ->
	let dcl = List.map fst dcl in
	let cnf = Cnf.make dcl in 
	ignore (Queue.fold (process_decl report) Explanation.empty cnf)
     ))
    declss
