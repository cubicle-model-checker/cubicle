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

open Preoptions


let _ = 
  Format.pp_set_tags fmt true;
  Print_color.add_to_format_tag fmt


let usage = "usage: alt-ergo [options] file.<mlw|smt>"

let spec = [
  "-rwt", Arg.Set rewriting, " use rewriting instead of axiomatic approach";
  "-parse-only", Arg.Set parse_only, " stop after parsing";
  "-smt-arrays", Arg.Set smt_arrays, " uses select/store symbols for Arrays";
  "-type-only", Arg.Set type_only , " stop after typing";
  "-notriggers", Arg.Set notriggers, "  trigger inference";
  "-debug", Arg.Set debug, "  sets the debugging flag";
  "-dcc", Arg.Set debug_cc, "  sets the debugging flag of cc";
  "-duse", Arg.Set debug_use, "  sets the debugging flag of use";
  "-duf", Arg.Set debug_uf, "  sets the debugging flag of uf";
  "-dfm", Arg.Set debug_fm, "  sets the debugging flag of Fourier-Moutzkin";
  "-dsum", Arg.Set debug_sum, "  sets the debugging flag of Sum";
  "-darith", Arg.Set debug_arith, 
  " sets the debugging flag of Arith (without fm)";
  "-dbitv", Arg.Set debug_bitv, "  sets the debugging flag of bitv";
  "-dac", Arg.Set debug_ac, "  sets the debugging flag of ac";
  "-dsat", Arg.Set debug_sat, "  sets the debugging flag of sat";
  "-dsats", Arg.Set debug_sat_simple, 
  "  sets the debugging flag of sat (simple output)";
  "-dtyping", Arg.Set debug_typing, "  sets the debugging flag of typing";
  "-types", Arg.Set debug_types, "  sets the debugging flag of types";
  "-dconstr", Arg.Set debug_constr, 
  "  sets the debugging flag of constructors";
  "-dpairs", Arg.Set debug_pairs, "  sets the debugging flag of pairs";
  "-darrays", Arg.Set debug_arrays, "  sets the debugging flag of arrays";
  "-dcombine", Arg.Set debug_combine, "  sets the debugging flag of combine";
  "-dsplit", Arg.Set debug_split, "  sets the debugging flag of case-split analysis";
   "-v", Arg.Set verbose, "  sets the verbose mode";
  "-version", Arg.Unit show_version, "  prints the version number";
  "-where", Arg.Unit show_libdir, "  prints the directory of the library";
  "-ddispatch", Arg.Set debug_dispatch, "  sets the debugging flag of sat";
  "-stop", Arg.Set_int stopb, " <n> set the stop bound";
  "-steps", Arg.Set_int stepsb, " <n> set the maximum number of steps";
  "-age-limite", Arg.Set_int age_limite, " <n> set the age limite bound";
  "-sat" , Arg.Set satmode , " mode sat/unsat";
  "-bj" , Arg.Set bjmode , " mode sat/unsat";
  "-glouton" , Arg.Set glouton, 
  " use ground terms in non-instanciated lemmas";
  "-redondance" , Arg.Set_int redondance, 
  " number of redondant (multi)triggers (2 by default)";
  "-select" , Arg.Set_int select, 
  "k tries to select relevant (at level k) hypotheses for each goal";
  "-triggers-var" , Arg.Set triggers_var , " allows variables as triggers";
  "-cctrace", Arg.Set_string tracefile, 
  " <file> set output file for cc trace ";
  "-no-rm-eq-existential", Arg.Set no_rm_eq_existential, " does not substitute a variable in an existential when an equality gives the value of the variable";
  "-astuce" , Arg.Set astuce, "";
  "-color" , 
  Arg.Unit (fun () -> Print_color.set_margin_with_term_width fmt;
              Print_color.disable false), "Set ainsi color in output";
  "-nocontracongru", Arg.Set nocontracongru, "";
  "-omega", Arg.Set omega, "Use omega for arithmetic equalities";
  "-arrays", Arg.Set arrays, "experimental support for the theory of arrays";
  "-pairs", Arg.Set pairs, "experimental support for the theory of pairs";
  "-term-like-pp", Arg.Set term_like_pp, "Output semantic values as terms";
  "-all-models", Arg.Set all_models, "experimental support for model";
  "-proof", Arg.Set proof, "experimental support for succint proof";
  "-debug-proof", Arg.Set debug_proof, "experimental support for succint proof";
  "-goal-directed", Arg.Set goal_directed,
   " instantiate lemmas only with the terms from the goal";
  "-bouclage", Arg.Set_int bouclage,
  " number of instantiations at each matching round";
  "-qualif", Arg.Set_int qualif, "<n> output rules used on stderr";
  "-vsid", Arg.Set vsid, "use VSID heuristic in SAT";
  "-max-split", Arg.String set_max_split,
  (Format.sprintf " maximum size of case-split (default value : %s)" 
     (Num.string_of_num !max_split));

]

let _ =
  let ofile = ref None in
  let set_file s =
    if Filename.check_suffix s ".mlw" || Filename.check_suffix s ".why"
    then ofile := Some s
    else
      if Filename.check_suffix s ".smt"
      then begin 
	smtfile := true ; ofile := Some s
      end
      else
	if Filename.check_suffix s ".smt2"
	then begin 
	  smt2file := true ; ofile := Some s
	end
	else raise (Arg.Bad "no .mlw, .smt or smt2 extension");
  in
  Arg.parse spec set_file usage;
  match !ofile with Some f -> file := f ; cin := open_in f 
    | None -> smt2file := true; cin := stdin
