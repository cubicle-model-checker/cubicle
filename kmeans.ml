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


let select_kmeans_deterministic arrays = 
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

let select_kmeans = 
  if deterministic then select_kmeans_deterministic 
  else select_kmeans_random

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

let clusterize set =
  let clusters = select_kmeans set in
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

let filter_clusters c =
  Clusters.fold (fun r l acc ->
    match l with 
      | [] | [_] -> acc
      | _ -> Clusters.add r l acc
  ) c Clusters.empty

let to_list c =
  Clusters.fold (fun r _ acc -> r :: acc) c []
    

let print_infos c =
  if verbose > 0 then (
    Printf.printf "Résultat \n";
    print_cluster c
  );
  let min_dist, max_dist = 
    Clusters.fold (fun k _ (mi, ma) ->
      let d = State.count_mones k in
      (if d < mi then d else mi),
      if d > ma then d else ma
    ) c (max_int, 0) in
  Printf.printf "Number of clusters : %d\n" (Clusters.cardinal c);
  Printf.printf "Minimum distance   : %d\n" min_dist;
  Printf.printf "Maximum distance   : %d\n" max_dist

let kmeans frg =
  let l = clusterize frg in
  let c = filter_clusters l in
  print_infos c;
  to_list c
    
