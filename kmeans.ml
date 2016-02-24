open Options

let () =
  if not deterministic then 
    if int_seed then Random.init seed 
    else Random.self_init ()
  
module Clusters = Map.Make (
  struct
    type t = State.t
    let compare = State.compare
  end
)

let print_cluster =
  Clusters.iter (fun k l ->
    Printf.printf "Représentant : "; 
    State.print "" k;
    Printf.printf "\tEnsemble :\n";
    List.iter (State.print "\t\t") l
  )

let select_kmeans_random arrays =
  let a = Array.of_list arrays in
  let l = List.length arrays in
  let nb_clusters = if nb_clusters > l then l else nb_clusters in
  let rec skm i max acc =
    if i < nb_clusters then
      let r = Random.int max in
      let e = Array.unsafe_get a r in
      let m1 = max - 1 in
      Array.unsafe_set a r (Array.unsafe_get a m1);
      if Clusters.exists (fun k _ -> State.distance k e = 0) acc then
        skm i m1 acc
      else
        skm (i+1) m1 (Clusters.add e [] acc)
    else acc
  in skm 0 (Array.length a) Clusters.empty

let select_kmeans_deterministic md arrays = 
  let min_distance a acc =
    Clusters.fold (fun k _ d ->
      let d' = State.distance a k in
      if d' < d then d' else d
    ) acc max_int
  in
  List.fold_left (fun acc s ->
    let d = min_distance s acc in
    if d > md then Clusters.add s [] acc
    else acc
  ) Clusters.empty arrays

let select_kmeans ?(md=0) = 
  if deterministic then select_kmeans_deterministic md
  else assert false

let add_to_cluster c e =
  let r, d = Clusters.fold (
    fun k _ (r, d) ->
      let d' = State.distance k e in
      if d' < d then (k, d')
      else (r, d)
  ) c (e, max_int) in
  let sr = Clusters.find r c in
  Clusters.add r (e :: sr) c
    
let adjust_means c =
  let change = ref false in
  let c = Clusters.fold (fun k l acc ->
    let m, l' = 
      match l with
        | [] -> k, []
        | k' :: l ->
          let z = State.copy k' in
          let m = List.fold_left (State.add_states) z l in
          if not (State.equal k m) then
            change := true;
          let l' = 
            try
              Clusters.find m acc
           with Not_found -> []
          in m, l'
    in
    Clusters.add m (List.rev_append l' l) acc
  ) c Clusters.empty in
  !change, c

let split_map c =
  Clusters.fold (fun k l (c, set) ->
    Clusters.add k [] c, List.rev_append l set
  ) c (Clusters.empty, [])

let clusterize ?(md=0) set =
  let clusters = select_kmeans ~md:md set in
  let rec crec c set =
    let c = List.fold_left add_to_cluster c set in
    let change, c = adjust_means c in
    if change then 
      (
        let c, set = split_map c in
        crec c set
      )
    else c
  in crec clusters set

let rec filter_clusters md c = 
  match filter_lvl with
    | 0 -> c
    | 1 -> 
      Clusters.fold (fun r l acc ->
        match l with
          | [] | [_] -> acc
          | _ -> Clusters.add r l acc
      ) c Clusters.empty
    | _ -> 
      Clusters.fold (fun r l acc ->
        let d = State.count_mones r in
        if d <= filter_md then Clusters.add r l acc
        else (
          (* Printf.printf "High distance : %d\n" d; *)
          let l = clusterize ~md:md l in
          (* print_cluster l; *)
          filter_clusters (md-1) l
        )
      ) c Clusters.empty

let to_list c =
  Clusters.fold (fun r c acc -> (r, c) :: acc) c []

let print_infos c =
  let min_dist, max_dist = 
    Clusters.fold (fun k _ (mi, ma) ->
      let d = State.count_mones k in
      (if d < mi then d else mi),
      if d > ma then d else ma
    ) c (max_int, 0) in
  Printf.printf "Number of clusters : %d\n" (Clusters.cardinal c);
  if Clusters.cardinal c > 0 then (
    Printf.printf "Minimum distance   : %d\n" min_dist;
    Printf.printf "Maximum distance   : %d\n" max_dist
  )

let kmeans ?(md=0) frg =
  let l = clusterize ~md:md frg in
  (* print_infos l; *)
  let c = filter_clusters md l in
  print_infos c;
  to_list c
    
