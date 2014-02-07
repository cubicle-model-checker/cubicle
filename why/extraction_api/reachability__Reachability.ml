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

let close_free_procs c =
  let procs_c =
    List.map (fun p -> p.Mlw_ty.pv_vs) (Translation.procs_of_why c) in
  let procs_ch = 
    List.map (fun v -> Hstring.make v.Term.vs_name.Ident.id_string) procs_c
  in
  let c = Term.t_and_simp (Translation.distinct_why procs_ch) c in
  Term.t_exists_close procs_c [] c

(* TODO ~ essayer conj post + unsafe *)
let get_post_trans e = match e.Mlw_expr.e_node with
  | Mlw_expr.Eapp (_, _, sp) -> 
     begin
       match sp.Mlw_ty.c_post.Term.t_node with
       | Term.Teps b ->
          let _, f = Term.t_open_bound b in
          f
       | _ -> assert false
     end
  | _ -> assert false 


let instantiate_trans t args =
  let e_args = List.map Mlw_expr.e_value args in
  Mlw_expr.e_app t e_args


let pre_one_trans t tr_args f =
  let f, _, _ = Translation.skolemize f in
  let procs_pvs = Translation.procs_of_why f in
  List.iter (eprintf "args : %a@." Mlw_pretty.print_pv) procs_pvs;
  let nargs = append_extra procs_pvs tr_args in
  let args_list = all_arrangements (List.length tr_args) nargs in
  List.fold_left (fun pre_f args ->
    let inst_t = instantiate_trans t args in
    (* let f = Term.t_and_simp (get_post_trans inst_t) f in *)
    eprintf "\npre %a\nBY %a\n===\n"
	    Pretty.print_term (Mlw_ty.create_post Translation.dummy_vsymbol f)
	    Mlw_pretty.print_expr inst_t;
    let kn = (!Global.global_module).Mlw_module.mod_known in
    let kt = (!Global.global_theory).Theory.th_known in
    let c = Mlw_wp.wp_expr Translation.env kn kt inst_t
			   (Mlw_ty.create_post Translation.dummy_vsymbol f)
			   Mlw_ty.Mexn.empty in
    (* let c = (Mlw_wp.remove_at c) in *)
    let c = Translation.simplify c in
    (* let c = Eval_match.eval_match ~inline:Eval_match.inline_nonrec_linear *)
    (*                               kt c in *)
    (* let c = Simplify_formula.fmla_cond_subst (fun t1 t2 -> t1 < t2) c in *)
    (* let c = Simplify_formula.fmla_remove_quant c in *)

    eprintf "%a\nafter dnf:@." Pretty.print_term c;

    List.fold_left (fun pre_f c ->
      let c = close_free_procs c in
      eprintf "%a@." Pretty.print_term c;
      (* assert false; *)
      Term.t_or_simp c pre_f
    ) pre_f (Translation.dnfize_list c)
  ) Term.t_false args_list


let pre (x: Fol__FOL.t) : Fol__FOL.t =
  (*-----------------  Begin manually edited ------------------*)
  List.fold_left 
    (fun pre_x (ft, tr_args) -> 
     Term.t_or_simp (pre_one_trans ft tr_args x) pre_x
    ) Term.t_false Global.sys_env.Global.s_trans
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


