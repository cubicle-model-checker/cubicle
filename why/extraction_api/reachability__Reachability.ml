(* This file has been generated from Why3 theory Reachability *)

module CPretty = Pretty
open Why3
open Ast
open Format


let append_extra args tr_args =
  let rec aux acc cpt = function
    | [] -> List.rev acc
    | _::r ->
       aux 
	 (Translation.proc_pvsymbol (List.nth proc_vars (cpt - 1)) :: acc)
	 (cpt+1) r
  in
  aux (List.rev args) (List.length args + 1) tr_args   

(* let nargs = append_extra args tr.tr_args *)

(* proc_pv_symbol #1 ... *)


let pre_one_trans t f =
  let f, _, _ = Translation.skolemize f in
  let procs_pvs = Translation.procs_of_why f in
  List.iter (eprintf "args : %a@." Mlw_pretty.print_pv) procs_pvs;
  let nargs = append_extra procs_pvs t.tr_args in
  let args_list = all_arrangements (List.length t.tr_args) nargs in
  List.fold_left (fun pre_f args ->
    eprintf "pre %a BY %a === "
	    Pretty.print_term (Term.t_eps_close Translation.dummy_vsymbol f)
	    Mlw_pretty.print_expr (Translation.instantiate_trans t args);
    let c = Mlw_wp.wp_expr Translation.env !Translation.known_map
			   (Translation.instantiate_trans t args)
			   (Term.t_eps_close Translation.dummy_vsymbol f)
			   Mlw_ty.Mexn.empty in
    let c =  (Mlw_wp.remove_at c) in
    List.fold_left (fun pre_f c ->
      let procs_c =
	List.map (fun p -> p.Mlw_ty.pv_vs) (Translation.procs_of_why c) in
      let procs_ch = 
	List.map (fun v -> Hstring.make v.Term.vs_name.Ident.id_string) procs_c in
      let c = Term.t_and_simp (Translation.distinct_why procs_ch) c in
      let c = Term.t_exists_close procs_c [] c in
      eprintf "%a@." Pretty.print_term c;
      Term.t_or_simp c pre_f
    ) pre_f (Translation.dnfize_list c)
  ) Term.t_false args_list


let pre (x: Fol__FOL.t) : Fol__FOL.t =
  (*-----------------  Begin manually edited ------------------*)
  List.fold_left (fun pre_x t -> Term.t_or_simp (pre_one_trans t x) pre_x)
		 Term.t_false (!Global.info).trans
  (*------------------  End manually edited -------------------*)

  (* ignore (Mlw_wp.wp_expr); *)
  (* let res_cubes =  *)
  (*   List.fold_left (fun acc s -> *)
  (*     let ls, post = Bwreach.pre_system s in *)
  (*     ls @ post @ acc *)
  (*   ) [] (Fol__FOL.fol_to_cubes x) *)
  (* in *)
  (* Fol__FOL.cubes_to_fol res_cubes *)




let pre_star (x: Fol__FOL.t) : Fol__FOL.t =
  failwith "to be implemented" (* uninterpreted symbol *)

let reachable (init: Fol__FOL.t) (f: Fol__FOL.t) : bool =
  (*-----------------  Begin manually edited ------------------*)
  Fol__FOL.sat (Fol__FOL.infix_et (pre_star f) init)
  (*------------------  End manually edited -------------------*)


