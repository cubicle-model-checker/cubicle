open Options
open Types
open Ast
open Far_modules
open Far_unwind

let graph = Far_graph.create ()

let queue = Q.create ()

let search system =
  let root, top = init_nodes system in
  Q.push root queue;
  let rec rsearch () =
    try
      let v1 = Q.pop queue in
      let trans = trans_from v1 in
      let ngraph = List.iter (
        fun t ->
          Far_graph.add_edge v1 t top graph;
          Far_unwind.unwind v1 t top
      ) trans in
      rsearch ()
    with Q.empty -> raise FSafe
  in
  rsearch ()
