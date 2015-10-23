let find_included_bads v graph = 
  let rec frec acc v =
    match Far_graph.find_refiners v2 graph with
      | [] -> acc
      | rs -> List.fold_left (fun acc r -> frec acc st :: acc) acc rs
  in frec [] v
        
  
let compute_pre t v = 
  List.fold_left (
    fun acc b -> 
      let nb = Node.create b in
      find_pre_node tr acc nb
  ) [] (List.rev_append bads obads)

let regroup = List.rev_append 

let select_procs slb v1 v2 =
  let gbd =
    let slb = List.fast_sort Far_util.compare_decr_cubes gbd in
    let rec group (cacc, acc, deg) = function
      | [] -> acc
      | hd :: tl ->
        let d = Cube.dim hd in
        if d = deg then group (hd::cacc, acc, deg)
        else 
          let acc =
            match cacc with 
              | [] -> acc
              | _ -> List.rev_append (deg, cacc) acc
          in group ([], acc, d)
    in group ([], [], 0) in
  let rec s l =
    match l with
      | [] -> assert false
      | hd :: _ ->
        let dim = Cube.dim hd in
        let less_proc, others = partition_l dim l in
        let nl = simplify_dnf v1.world v2.bad less_proc in
        match nl with
          | [] -> s others
          | _ -> Stats.cpt_process := max Stats.(!cpt_process) dim; nl
  in s lb


let select_parts bad_parts v1 v2 =
  select_procs pre_image v1 v2
       
