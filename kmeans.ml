let int_seed = ref false
let seed = ref 0

let set_seed n =
  int_seed := true;
  seed := n

let nb_arrays = ref 10
let size_array = ref 4
let max_int = ref 10

let dist_type = ref "h"

let nb_clusters = ref 4

let usage = "usage: ./kmeans"

let deterministic = ref false
let md = ref 0

let provided = ref false
let frg_file = ref ""

let save_cluster = ref false
let clu_file = ref ""

let set_frgfile s =
  provided := true;
  if Filename.check_suffix s ".frg" then frg_file := s
  else raise (Arg.Bad "no .frg extension")

let set_deterministic n =
  deterministic := true;
  md := n

let specs = 
  [ "-seed", Arg.Int set_seed , "<n> seed for rng";
    "-na", Arg.Set_int nb_arrays, "<n> number of generated arrays";
    "-sa", Arg.Set_int size_array, "<n> size of each array";
    "-mi", Arg.Set_int max_int, "<n> maximum positive integer";
    "-dist", Arg.Set_string dist_type, "<h|e> hamming(default) or euclid distance";
    "-k", Arg.Set_int nb_clusters, "<n> number of clusters";
    "-det", Arg.Int set_deterministic, "<n> deterministic method to find k with a max distance";
    "-file", Arg.String set_frgfile, " provides an array of states";
    "-save", Arg.Set save_cluster, " save the clusters in a *.clu file";
  ]

let alspecs = Arg.align specs

let () = Arg.parse alspecs (fun _ -> ()) usage

let int_seed = !int_seed
let seed = !seed

let nb_arrays = !nb_arrays
let size_array = !size_array
let max_int = !max_int

let dist_type = !dist_type

let nb_clusters = !nb_clusters

let deterministic = !deterministic
let md = float !md

let provided = !provided
let frg_file = !frg_file

let save_cluster = !save_cluster

let () =
  if not deterministic then 
    if int_seed then Random.init seed 
    else Random.self_init ()
  
let () =
  if save_cluster then
    if Filename.check_suffix frg_file ".frg" 
    then let s = Filename.chop_suffix frg_file ".frg" in
         clu_file := Printf.sprintf "%s-%s.clu" s 
           (if deterministic then Printf.sprintf "det_%.0f" md 
            else Printf.sprintf "rand_%d" (Random.int 1000))
    else raise (Arg.Bad "no .clu extension")

let clu_file = !clu_file

let () = Printf.printf "seed : %b\n" int_seed

module type FA = sig
  type t

  val empty : int -> t

  val empty_from_fa : t -> t

  val fa_from_fl : float list -> t

  val length : t -> int
    
  val distance : t -> t -> float

  val add_arrays : t -> t -> t

  val normalize : t -> t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val print : string -> t -> unit

  val print_fmt : out_channel -> t -> unit
    
  val array_to_fa : float array -> t
end

module FloatArray : FA = struct
  type t = (float * int) array

  let length = Array.length

  let empty n = Array.make n (-1., 0)

  let empty_from_fa k =
    match dist_type with
      | "h" -> Array.copy k
      | "e" -> Array.make (length k) (-1., 0)
      | _ -> raise (Arg.Bad "no distance with this name")

  let fa_from_fl fl =
    let a = Array.of_list fl in
    Array.map (fun f -> (f, 1)) a

  (* It's tricky here. The arrays have values above 0. When it's -1 it means it can
     be any positive value.
  *)
  let euclid_distance t1 t2 =
    let d = ref 0. in
    Array.iteri (fun i (e1, _) ->
      let e2, _ = t2.(i) in
      if e1 <> -1. && e2 <> -1. then
        let di = e1 -. e2 in
        d := !d +. (di *. di)
    ) t1;
    sqrt !d

  let hamming_distance t1 t2 =
    let d = ref 0 in
    let star = ref 0 in
    Array.iteri (fun i (e1, _) ->
      let e2, _ = t2.(i) in
      if e1 = -1. || e2 = -1. then star := 1
      else if e1 <> e2 then incr d
    ) t1;
    float (!d + !star)

  let distance = 
    match dist_type with
      | "h" -> hamming_distance
      | "e" -> euclid_distance
      | _ -> raise (Arg.Bad "no distance with this name")

  let add_arrays_euclid t1 t2 = 
    Array.mapi (
      fun i (e1, m) -> 
        let (e2, m') = t2.(i) in
        match e1, e2 with
          | -1., _ -> (e2, m')
          | _, -1. -> (e1, m) 
          | _ -> (e1 +. e2, m + m')
    ) t1

  let add_arrays_hamming t1 t2 = 
    Array.mapi (
      fun i (e1, _) -> 
        let (e2, _) = t2.(i) in
        let (d, _) = match e1, e2 with
          | -1., e | e, -1. -> (-1., 1)
          | _ when e1 = e2 -> (e1, 1)
          | _ -> (-1., 1) in
        (* if d = -1. then Printf.printf "%.1f %.1f\n" e1 e2; *)
        (d, 1)
    ) t1

  let add_arrays = 
    match dist_type with
      | "h" -> add_arrays_hamming
      | "e" -> add_arrays_euclid
      | _ -> raise (Arg.Bad "no distance with this name")

  let normalize_euclid t1 = 
    Array.map (fun (e, m) -> if e = -1. then (e, 1) else (e /. float m, 1)) t1

  let normalize_hamming t1 = t1

  let normalize = 
    match dist_type with
      | "h" -> normalize_hamming
      | "e" -> normalize_euclid
      | _ -> raise (Arg.Bad "no distance with this name")


  let compare t1 t2 = 
    let m = length t1 in
    let rec rc i =
      if i = m then 0
      else let e1, _ = t1.(i) in
           let e2, _ = t2.(i) in
           if e1 = e2 then rc (i+1)
           else Pervasives.compare e1 e2
    in rc 0
    
  let equal t1 t2 = compare t1 t2 = 0

  let print sep t1 =
    Printf.printf "%s[|" sep;
    Array.iter (fun (e, _) -> Printf.printf "%.0f " e) t1;
    Printf.printf "|]\n"

  let print_fmt fmt t =
    Array.iter (fun (e, _) -> Printf.fprintf fmt "%.0f;" e) t

  let array_to_fa a =
    Array.map (fun e -> (e, 1)) a



end
  
module AMap = Map.Make (FloatArray)

let print_cluster =
  AMap.iter (fun k l ->
    Printf.printf "Représentant : "; 
    FloatArray.print "" k;
    Printf.printf "\tEnsemble :\n";
    List.iter (FloatArray.print "\t\t") l
  )

let select_kmeans_random arrays =
  let a = Array.of_list arrays in
  let rec skm i max acc =
    if i < nb_clusters then
      let r = Random.int max in
      let e = Array.unsafe_get a r in
      let m1 = max - 1 in
      Array.unsafe_set a r (Array.unsafe_get a m1);
      if AMap.exists (fun k _ -> FloatArray.distance k e = 0.) acc then
        skm i m1 acc
      else
        skm (i+1) m1 (AMap.add e [] acc)
    else acc
  in skm 0 (Array.length a) AMap.empty


let select_kmeans_deterministic arrays = 
  let min_distance a acc =
    AMap.fold (fun k _ d ->
      let d' = FloatArray.distance a k in
      if d' < d then d' else d
    ) acc infinity
  in
  let rec skd l acc =
    match l with
      | [] -> acc
      | a :: tl ->
        let acc = 
          let d = min_distance a acc in
          if d > md then AMap.add a [] acc
          else acc
        in skd tl acc
  in skd arrays AMap.empty

let select_kmeans = 
  if deterministic then select_kmeans_deterministic 
  else select_kmeans_random

let add_to_cluster c e =
  let r, d = AMap.fold (
    fun k _ (r, d) ->
      let d' = FloatArray.distance k e in
      if d' < d then (k, d')
      else (r, d)
  ) c (e, infinity) in
  let sr = AMap.find r c in
  AMap.add r (e :: sr) c

    
let adjust_means c =
  let change = ref false in
  let c = AMap.fold (fun k l acc ->
    let m = 
      match l with
        | [] -> k
        | k' :: l ->
          let z = FloatArray.empty_from_fa k' in
          let m = List.fold_left (FloatArray.add_arrays) z l in
          let m = FloatArray.normalize m in
          if not (FloatArray.equal k m) then
            change := true;
          (try
             assert (not (AMap.mem m acc))
           with Assert_failure _ -> 
             print_cluster c;
             List.iter (FloatArray.print "l: ") l;
             FloatArray.print "\tm:" m; exit 1
          );
          m
    in
    AMap.add m l acc
  ) c AMap.empty in
  !change, c

let split_map c =
  AMap.fold (fun k l (c, set) ->
    AMap.add k [] c, List.rev_append l set
  ) c (AMap.empty, [])

let clusterize set =
  let clusters = select_kmeans set in
  (* let set' = Array.of_list set in *)
  (* let clusters = AMap.add set'.(0) [] (AMap.add set'.(3) [] (AMap.singleton set'.(6) [])) in *)
  Printf.printf "Initial Cluster :\n";
  print_cluster clusters;
  Printf.printf "End\n";
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

let init_arrays () =
  let rec ri i acc =
    if i = nb_arrays then acc
    else let a = Array.init size_array (fun _ -> float (Random.int max_int - 1)) in
         let fa = FloatArray.array_to_fa a in
         ri (i+1) (fa::acc)
  in ri 0 []

let parse_file () =
  let ci = open_in frg_file in
  let re = Str.regexp ";" in
  let set = ref [] in
  (try
    while true do
      let l = input_line ci in
      let sl = Str.split re l in
      let fl = List.map (float_of_string) sl in
      let fa = FloatArray.fa_from_fl fl in
      set := fa :: !set
    done
  with End_of_file -> ());
  !set

let save_clu c =
  let oc = open_out clu_file in
  AMap.iter (fun r l ->
    match l with 
      | [] | [_] -> ()
      | _ ->
        Printf.fprintf oc "%a" FloatArray.print_fmt r;
        Printf.fprintf oc "\n"
  ) c;
  close_out oc

let () = 
  (* let a1 = [|2.; 2.; 2.|] in *)
  (* let a2 = [|2.; 1.; 2.|] in *)
  (* let a3 = [|2.; 3.; 2.|] in *)
  (* let a4 = [|3.; 3.; 3.|] in *)
  (* let a5 = [|3.; 2.; 3.|] in *)
  (* let a6 = [|3.; 4.; 3.|] in *)
  (* let a7 = [|6.; 1.; 4.|] in *)
  (* let l = List.map (FloatArray.array_to_fa) [a1; a2; a3; a4; a5; a6; a7] in *)
  let l = if provided then parse_file () else init_arrays () in
  let c = clusterize l in
  Printf.printf "Résultat \n";
  print_cluster c;
  if save_cluster then save_clu c
  (* List.iter (FloatArray.print "") l' *)
    
    
