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

open Lexing
open Format
open Options
open Ast
open Why3


let set_gc_control =
  let gc_c = Gc.get() in
  let gc_c =
    { gc_c with
        (* Gc.verbose = 0x3FF; *)
        Gc.minor_heap_size = 32000000; (* default 32000*)
        (*major_heap_increment = 0;    (* default 124000*)*)
        space_overhead = 80; (* default 80% des donnes vivantes *)
    }
  in
  Gc.set gc_c

let report (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  printf "File \"%s\", line %d, characters %d-%d:" file l fc lc


let env = Translation.env

let get_unsafe m =
  let uf = Mlw_module.ns_find_ps m.Mlw_module.mod_export ["unsafe"] in
  uf.Mlw_expr.ps_aty.Mlw_ty.aty_spec.Mlw_ty.c_pre

let get_init m =
  let uf = Mlw_module.ns_find_ps m.Mlw_module.mod_export ["init"] in
  let _, i =
    Mlw_ty.open_post (uf.Mlw_expr.ps_aty.Mlw_ty.aty_spec.Mlw_ty.c_post) in
  i


let make_arrow t_ps t_args =
  let ty_args = List.map (fun a -> a.Mlw_ty.pv_ity) t_args in
  Mlw_expr.e_arrow t_ps ty_args Mlw_ty.ity_unit

let get_transitions m =
  Ident.Mid.fold 
    (fun id d acc ->
     try 
       Scanf.sscanf id.Ident.id_string "transition_%s" (fun _ -> ());
       match d.Mlw_decl.pd_node with
       | Mlw_decl.PDrec [fd] ->
          let t_ps = fd.Mlw_expr.fun_ps in
          let t_args = fd.Mlw_expr.fun_lambda.Mlw_expr.l_args in
          let arrow = make_arrow t_ps t_args in
          printf "Found transition: %a@." Mlw_pretty.print_expr arrow;
          (arrow, t_args) :: acc
       | _ -> assert false
     with Scanf.Scan_failure _ -> acc
    ) (m.Mlw_module.mod_known) []


let init_smt th m =
try
  (* List.iter  *)
  (*   (fun n -> Smt.Symbol.declare n [] Smt.Type.type_proc) *)
  (*   proc_vars; *)

   List.iter 
     (fun d ->
      match d.Theory.td_node with
      | Theory.Decl d -> 
         begin
           match d.Decl.d_node with
           | Decl.Dtype t ->
              let n = t.Ty.ts_name.Ident.id_string in
              if n <> "proc" then Smt.Type.declare (Hstring.make n) []
           | Decl.Ddata [t, cstrs] ->
              let n = t.Ty.ts_name.Ident.id_string in
              let h_cstrs = 
                List.map (fun (c, _) -> 
                          let cn = c.Term.ls_name.Ident.id_string in
                          Hstring.make cn
                         ) cstrs in
              eprintf "DECL %s@." n;
              Smt.Type.declare (Hstring.make n) h_cstrs
           | _ -> ()
         end
      | _ -> ()
     ) th.Theory.th_decls;
 
   let assoc_types = 
   List.fold_left 
     (fun acc d ->
      eprintf "exam decl : %a@." Mlw_pretty.print_pdecl d;
      match d.Mlw_decl.pd_node with
      | Mlw_decl.PDval (Mlw_expr.LetV pvs) ->
         let n = pvs.Mlw_ty.pv_vs.Term.vs_name.Ident.id_string in
         begin 
           match pvs.Mlw_ty.pv_ity.Mlw_ty.T.ity_node with
           | Mlw_ty.T.Ityapp (_, [it], _) ->
              
              eprintf "REF : %a@." Mlw_pretty.print_pdecl d;
              begin
                match it.Mlw_ty.T.ity_node with
                | Mlw_ty.T.Itypur (s, []) ->
                   (* Global variable : ref tys *)
                   let tyn = s.Ty.ts_name.Ident.id_string in
                   Smt.Symbol.declare (Hstring.make n) [] (Hstring.make tyn);
                   (Hstring.make n, Hstring.make tyn) :: acc
                | Mlw_ty.T.Itypur (_, [itf; it]) ->
                   (* Array variable : ref (map itf it) and we know itf is proc *)
                   let tyn = match it.Mlw_ty.T.ity_node with
                     | Mlw_ty.T.Itypur (s, _) ->
                        s.Ty.ts_name.Ident.id_string
                     | _ -> assert false
                   in
                   Smt.Symbol.declare (Hstring.make n)
                                      [Smt.Type.type_proc] (Hstring.make tyn);
                   (Hstring.make n, Hstring.make tyn) :: acc
                   
                | _ -> assert false
              end
           | _ ->
              eprintf "DD : %a@." Mlw_pretty.print_pdecl d;
              assert false
         end
      | _ -> acc
                               
     ) [] (m.Mlw_module.mod_decls) in

   Smt.Variant.init assoc_types

with
  | Smt.Error (Smt.DuplicateSymb _) -> assert false
  | Smt.Error (Smt.DuplicateTypeName n) -> eprintf "dup %a@." Hstring.print n;
                                           assert false
  | Smt.Error (Smt.UnknownSymb _) -> assert false
  | Smt.Error (Smt.UnknownType n) -> eprintf "unk %a@." Hstring.print n;
                                     assert false


let _ = 
  let lb = from_channel cin in 
  begin
    (* try *)
    
    
    (* TODO petit test *)
    
    let lib = Mlw_main.library_of_env env in
    
    let pathname = [] (* dummy pathname *)in
    
    let t : Ptree.incremental =
      Mlw_typing.open_file lib (Env.get_loadpath env) in
    
    let mm, thm = Mlw_main.read_channel lib [] file cin in
    
    let m = match Stdlib.Mstr.values mm with
      | [m] -> m
      | _ -> failwith "There can only be one module inside a file."
    in

    let th = match Stdlib.Mstr.values thm with
      | [th] -> th
      | _ -> failwith "There can only be one theory inside a file."
    in


    (* Initialze types and symbols for the SMT solver *)
    init_smt th m;

    Global.sys_env.s_init <- (get_init m);
    Global.sys_env.s_unsafe <- (get_unsafe m);
    Global.sys_env.s_trans <- (get_transitions m);
    

    match Cubicle_brab_map__Cubicle_BRAB.brab
            Global.sys_env.s_init
            Global.sys_env.s_unsafe with
    | Cubicle_brab_map__Cubicle_BRAB.Safe ->
       printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@.";
       printf "timer: %f s@." (Prover.TimeF.get ());
    | Cubicle_brab_map__Cubicle_BRAB.Unsafe ->
       printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@."; exit 1
    

    (*   let s = Parser.system Lexer.token lb in *)
    (*   let ts = Typing.system s in *)
    (*   let ts = List.map Bwreach.init_parameters ts in *)
    (*   Global.global_system := List.hd ts; *)
    (*   Global.info := s; *)
    (*   Translation.set_decl_module s; *)
    (*   (\* Fol__FOL.init_declarations s; *\) *)
    (*   if type_only then exit 0; *)

    (*   let procs = Forward.procs_from_nb enumerative in *)
    (*   eprintf "STATEFULL ENUMERATIVE FORWARD :\n-------------\n@."; *)
    (*   Enumerative.search procs !Global.global_system; *)
    (*   eprintf "-------------\n@."; *)
    
    (*   let theta = match ts with  *)
    (*     | [] -> assert false *)
    (*     | _ -> Fol__FOL.cubes_to_fol ts  *)
    (*   in *)
    (*   let init = Fol__FOL.init_to_fol !Global.global_system in *)
    (*   match Cubicle_brab_map__Cubicle_BRAB.brab init theta with *)
    (*   | Cubicle_brab_map__Cubicle_BRAB.Safe -> *)
    (*      printf "\n\nThe system is @{<b>@{<fg_green>SAFE@}@}\n@."; *)
    (*      printf "timer: %f s@." (Prover.TimeF.get ()); *)
    (*   | Cubicle_brab_map__Cubicle_BRAB.Unsafe -> *)
    (*      printf "\n\n@{<b>@{<bg_red>UNSAFE@} !@}\n@."; exit 1 *)
							     
							     
    (* with *)
    (* | Lexer.Lexical_error s ->  *)
    (*    report (lexeme_start_p lb, lexeme_end_p lb); *)
    (*    printf "lexical error: %s\n@." s; *)
    (*    exit 2 *)
    (* | Parsing.Parse_error -> *)
    (*    let  loc = (lexeme_start_p lb, lexeme_end_p lb) in *)
    (*    report loc; *)
    (*    printf "\nsyntax error\n@."; *)
    (*    exit 2 *)
    (* | Typing.Error e ->  *)
    (*    printf "typing error: %a\n@." Typing.report e; *)
    (*    exit 2 *)

  end
