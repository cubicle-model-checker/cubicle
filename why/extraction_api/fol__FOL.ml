(* This file has been generated from Why3 theory FOL *)
open Ast
open Global
open Format
module S = Set__Fset

open Why3

type t = Term.term

(* let compare = Term.compare *)


let rec print = Why3.Pretty.print_term

(* type structure to be defined (uninterpreted type) *)

(* let infix_breq (x: structure) (x1: t) : bool = *)
(*   failwith "to be implemented" (\* uninterpreted symbol *\) *)

let ffalse  : t = Term.t_false

let ttrue  : t = Term.t_true


(* let declarations_task = ref None *)

(* let init_declarations s = *)
(*   declarations_task :=  *)
(*     List.fold_left (fun task (x,y) -> *)
(* 		    let tys = Ty.create_tysymbol *)
(* 				(Ident.id_fresh (Hstring.view x)) *)
(* 				[] None in *)
(* 		    match y with *)
(* 		    | [] -> Task.add_ty_decl task tys *)
(* 		    | _ ->  *)
(* 		       let constrs =  *)
(* 			 List.map (fun s -> *)
(* 				   Term.create_lsymbol  *)
(* 				     (Ident.id_fresh (Hstring.view s)) *)
(* 				     [] None, []) y in *)
(* 		       Task.add_data_decl task [tys, constrs] *)
(* 		   ) !declarations_task s.type_defs; *)
(*   declarations_task := *)
(*     List.fold_left  *)
(*       (fun task (n, t) -> *)
(*        let ty = Ty.ty_app (Ty.create_tysymbol *)
(* 		   (Ident.id_fresh (Hstring.view n)) *)
(* 		   [] None) [] in *)
(*        let f = Term.create_fsymbol (Ident.id_fresh (Hstring.view n)) [] ty in *)
(*        Task.add_param_decl task f *)
(*       ) !declarations_task (s.consts @ s.globals); *)
(*   declarations_task := *)
(*     List.fold_left  *)
(*       (fun task (n, (args, ret)) -> *)
(*        let ty_ret = Ty.ty_app (Ty.create_tysymbol *)
(* 		   (Ident.id_fresh (Hstring.view ret)) *)
(* 		   [] None) []  in *)
(*        let ty_args = List.map (fun t-> Ty.ty_app (Ty.create_tysymbol *)
(* 		   (Ident.id_fresh (Hstring.view t)) *)
(* 		   [] None) []) args in *)
(*        let f = Term.create_fsymbol (Ident.id_fresh (Hstring.view n)) *)
(* 				   ty_args ty_ret in *)
(*        Task.add_param_decl task f *)
(*       ) !declarations_task s.arrays *)


(* let init_to_fol ({t_init = args, lsa} as i) = *)
(*   let r = Translation.init_to_fol i in *)
(*   if Options.debug then *)
(*   (List.iter (fun sa -> eprintf "init: %a ===> @." Pretty.print_cube sa) lsa; *)
(*    eprintf "         ===> %a @." print r); *)
(*   r *)


let init_to_fol = Translation.init_to_fol


let fol_to_cubes = Translation.why_to_systems

let cubes_to_fol = Translation.systems_to_why

	
(* neg *)  
let prefix_tl (x: t) : t = Term.t_not_simp x

let infix_et (x: t) (x1: t) : t = Term.t_and_simp x x1

let infix_plpl (x: t) (x1: t) : t =  Term.t_or_simp x x1

let infix_eqgt (x: t) (x1: t) : t = Term.t_implies_simp x x1


(* let infix_breqeq (x: t) (x1: t) : bool = *)
(*   if Options.debug then eprintf "do: %a  |=  %a@." print x print x1; *)

(*   let f = infix_eqgt x x1 in *)

(*   let goal_id = Decl.create_prsymbol (Ident.id_fresh "goal") in *)
(*   let task = Task.add_prop_decl !declarations_task Decl.Pgoal goal_id f in *)

(*   assert false *)

let infix_breqeq (x: t) (x1: t) : bool =
  if Options.debug then eprintf "do: %a  |=  %a@." print x print x1;
  (* let x, x1 = dnfize x, dnfize x1 in  *)
  let ls = fol_to_cubes x in
  match ls with
  | [s] -> Cube.fixpoint ~invariants:[] ~visited:(fol_to_cubes x1) s <> None
  | _ -> assert false

(* Notataions *)

let neg = prefix_tl

let (&) x x1 = infix_et x x1

let (++) x x1 = infix_plpl x x1

let (=>) x x1 = infix_eqgt x x1
  
let (|=) x x1 = infix_breqeq x x1



module SMT = Prover.SMT

let sat (f: t) : bool =
  if Options.debug then eprintf "sat: %a@." print f;
  List.exists (fun (dist, f) ->
	       try
		 SMT.clear ();
		 SMT.assume ~profiling:false ~id:0 dist;
		 SMT.assume ~profiling:false ~id:0 f;
		 SMT.check  ~profiling:false ();
		 true
	       with Smt.Unsat _ -> false 
	      ) (Translation.safety_formulas f)

let valid (f: t) : bool = not (sat (prefix_tl f))
