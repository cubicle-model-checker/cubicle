open Ast
open Far_modules.Vertex

let print_bads bl =
  List.iter (
    fun n -> Format.eprintf "\t\tExists %a, @[%a@] AND\n@." 
      Variable.print_vars (Far_cube.variables n)
      (Types.SAtom.print_sep "&&") (Far_cube.litterals n)
  ) bl    

let find_included_bads v graph = 
  Format.eprintf "Find_incl @.";
  let rec frec acc v =
    match Far_graph.find_refiners v graph with
      | [] -> acc
      | rs -> List.iter (Format.eprintf "%a " print_id) rs;
        List.fold_left (
          fun acc r -> let acc = List.rev_append r.bad acc in
                       frec acc r
        ) acc rs
  in 
  let l = frec [] v in
  Format.eprintf "\nEnd Find_incl @.";
  l
  

let regroup = List.rev_append 


let simplify_dnf w1 b2 dnf =
  let nw1 = Far_cube.negate_litterals_to_ecubes w1 in
  let sdnf = List.fold_left (
    fun acc cube ->
      let cig = Far_cube.cube_implies cube nw1 in
      match cig with 
        | Some _ -> acc
        | None ->
          let cib = Far_cube.cube_implies cube b2 in
          match cib with
            | Some c -> c::acc
            | None -> 
              match Fixpoint.FixpointList.check cube acc with
                | None -> cube::acc
                | Some l -> acc
  ) [] dnf in
  sdnf


let select_procs slb v1 v2 =
  let gbd =
    let slb = List.fast_sort Far_cube.compare_decr_fcubes slb in
    let slb = Far_cube.filter slb in
    let rec group (actual_group, done_group, dim) = function
      | [] -> (
        match actual_group with 
          | [] -> done_group
          | _ -> (dim, actual_group) :: done_group
      )
      | hd :: tl ->
        let d = Far_cube.dim hd in
        if d = dim then group (hd::actual_group, done_group, dim) tl
        else 
          let done_group =
            match actual_group with 
              | [] -> done_group
              | _ -> (dim, actual_group) :: done_group
          in group ([hd], done_group, d) tl
    in group ([], [], 0) slb in
  let rec s l =
    match l with
      | [] -> assert false
      | (dim, lcubes) :: st ->
        let nl = simplify_dnf v1.world v2.bad lcubes in
        match nl with
          | [] -> s st
          | _ -> nl
  in s gbd

(* let partition_l dim l = *)
(*   let rec f acc ll = *)
(*     match ll with  *)
(*       | hd::tl when (Far_cube.dim hd) = dim -> f (hd::acc) tl *)
(*       | _ -> acc, ll *)
(*   in f [] l *)


(* let select_procs lb v1 v2 = *)
  
(*   (\* Format.eprintf "[Select procs]\n%a@." print_ednf l; *\) *)
(*   let rec s l = *)
(*     match l with *)
(*       | [] -> assert false *)
(*       | hd::tl -> *)
(*         let dim = Far_cube.dim hd in *)
(*         let less_proc, others = partition_l dim l in *)
(*         let nl = simplify_dnf v1.world v2.bad less_proc in *)
(*         match nl with *)
(*           | [] -> s others *)
(*           | _ -> nl *)
(*   in s lb *)


let select_parts v1 t v2 bp graph system  =
  let ob = find_included_bads v2 graph in
  let pob = Far_util.compute_pre t ob in
  let fpob = Far_cube.filter pob in
  let allb = regroup bp fpob in
  (* Format.eprintf "Allb@."; *)
  (* print_bads allb; *)
  (* Format.eprintf "End Allb@."; *)
  let selb = select_procs allb v1 v2 in
  (* Format.eprintf "Selb@."; *)
  (* print_bads selb; *)
  (* Format.eprintf "End Selb@."; *)
  let bp =
    if Options.far_brab then
      let slb = List.fast_sort Far_cube.compare_decr_fcubes allb in
      List.map (fun nb ->
        match Approx.Selected.good nb with
          | None -> nb
          | Some c ->
            try
              (* Replace node with its approximation *)
              Safety.check system c;
              (* candidates := c :: !candidates; *)
              Stats.candidate nb c;
              (* Format.eprintf
                 "Approximation : \n%a ->  \n%a@." Node.print nb Node.print c; *)
              c
            with Safety.Unsafe _ -> nb
            (* If the candidate is directly reachable, no need to
               backtrack, just forget it. *)
            (* if ic3_verbose > 0 then *)
      ) slb
    else selb in
  List.iter Stats.new_node bp;
  bp
