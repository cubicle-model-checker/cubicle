open Options
open Cubtypes
open Ast
open Far_modules

type result = FUnsafe | FSafe

let graph = Far_graph.create 17

let init_nodes system =
  let u = system.t_unsafe in
  let top = Vertex.create [] [] u in
  List.iter Stats.new_node u;
  let (_, initfl) = system.t_init in
  let initf = match initfl with
      | [e] -> e
      | _ -> assert false
  in
  let initl =
    SAtom.fold (
        fun a acc -> (
	  Variable.Set.elements (Atom.variables a),
	  SAtom.singleton a
        )::acc
      ) initf [] in
  let wroot = Vertex.create_world initl in
  let broot = Vertex.create_bad [] in
  (* Create root with groot, broot and no subsume *)
  let root = Vertex.create ~is_root:true wroot wroot broot in
  root, top

let search system =
  if far_extra = "oracle" || do_brab then Oracle.init system;
  if only_forward then exit 0;

  let root, top = init_nodes system in
  Q.push root queue;

  let trans = system.t_trans in
  let trans_from = Far_modules.init_trans_from trans in

  let rec rsearch () =
    try
      let v1 = Q.pop queue in

      let bads = ref [] in
      (* Format.eprintf "Trans from@."; *)
      (* Format.eprintf "End Trans from@."; *)
      Format.eprintf "***************************@.";
      Format.eprintf "******* Search %a *********@." Vertex.print_id v1;
      Format.eprintf "***************************\n@.";
      (* Far_graph.list_trans_to v1 graph; *)
      let tm = Far_graph.trans_map v1 graph in
      let trans = trans_from v1 in
      if verbose > 0 then Format.eprintf "\n%a@." Vertex.print_world v1;

      (try
        List.iter (
          fun t ->
            let v2 =
              match Far_graph.get_node t tm with
                | Some v -> v
                | None -> top
            in
            Far_graph.add_edge v1 t v2 graph;
            try
              Far_unwind.unwind v1 t v2 graph system
            with
              | Far_unwind.Bad e -> bads := e :: !bads
        ) trans;
        (match !bads with
          | [] -> ()
          | l -> Far_unwind.propagate v1 l graph system);
      with Far_unwind.PropBad b -> Far_unwind.prop v1 b graph system);
      rsearch ()
    with
      | Q.Empty -> FSafe
      | Exit -> FUnsafe
  in
  rsearch ()
