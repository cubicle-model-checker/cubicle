type t = int array

(* useful functions for clustering *)

let hamming_distance t1 t2 =
    let d = ref 0 in
    let star = ref 0 in
    Array.iteri (fun i e1 ->
      let e2 = t2.(i) in
      if e1 = -1 || e2 = -1 then star := 1
      else if e1 <> e2 then incr d
    ) t1;
    (!d + !star)

let distance = hamming_distance

let count_mones t =
    Array.fold_left (fun c e -> if e = -1 then c + 1 else c) 0 t

let add_states_hamming t1 t2 = 
  Array.mapi (
    fun i e1 -> 
      let e2 = t2.(i) in
      let d = match e1, e2 with
        | -1, e | e, -1 -> -1
        | _ when e1 = e2 -> e1
        | _ -> -1 in
        (* if d = -1. then Printf.printf "%.1f %.1f\n" e1 e2; *)
      d
  ) t1

let add_states = add_states_hamming

let compare t1 t2 = 
  let m = Array.length t1 in
  let rec rc i =
    if i = m then 0
    else let e1 = t1.(i) in
         let e2 = t2.(i) in
         if e1 = e2 then rc (i + 1)
         else Pervasives.compare e1 e2
  in rc 0
  
let equal t1 t2 = compare t1 t2 = 0

let copy = Array.copy

let print sep t1 =
  Printf.printf "%s[|" sep;
  Array.iter (Printf.printf "%d ") t1;
  Printf.printf "|]\n"
