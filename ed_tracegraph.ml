open Ed_graph 

module HT  = 
  Hashtbl.Make
    (struct 
      type t = string
      let equal x y = (String.trim x) = (String.trim y) 
      let hash x  = Hashtbl.hash x 
    end)

let rec node_name  = function
  |[] -> ""
  |x::[] -> 
    (match Str.split (Str.regexp "\n") (String.trim x) with
      |[] -> failwith "pb format trace"
      |y::_ ->  y)
  |x::s -> (String.trim x)^"\n"^(node_name s)

        
let load_graph str  =
  let g = B.empty() in
  let h = HT.create 100 in
  let l = Str.split (Str.regexp "==") str in
  match l with 
    |[] -> failwith "pb format trace"
    |s::t -> 
      let str_l = Str.split (Str.regexp "node [0-9]+:") (String.trim s) in
      List.iter (fun x ->
        let pos = Str.search_forward (Str.regexp "=") x 0 in
        let before = Str.global_replace (Str.regexp "[\n| ]+") "" ( String.trim (Str.string_before x pos)) in
        let after = node_name (Str.split (Str.regexp "&&") (Str.string_after x (pos + 1))) in
        let v = G.V.create (make_node_info after ) in
        B.G.add_vertex g v;
        HT.add h before v;
        try
          let arrow_pos = Str.search_forward (Str.regexp "->") before 0 in
          let transition = Str.string_before before arrow_pos in
          let node = Str.global_replace (Str.regexp "[\n| ]+") ""  (Str.string_after before (arrow_pos + 2)) in
          let n = HT.find h node in
          let e = G.E.create n (make_edge_info_label transition) v in
          B.G.add_edge_e g e;
        with Not_found -> ()
      ) str_l;
      g
