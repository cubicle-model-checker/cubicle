
module H = Hstring

let compare_hpair (x1,y1) (x2,y2) = (* duplicate Weakmem.H2.compare *)
  let c = H.compare x1 x2 in
  if c <> 0 then c else H.compare y1 y2

let rec compare_hplist l1 l2 = match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: r1, y :: r2 ->
     let c = compare_hpair x y in
     if c <> 0 then c else compare_hplist r1 r2

let rec equal_hplist hpl1 hpl2 = match hpl1, hpl2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | (hl1, hr1) :: hpl1, (hl2, hr2) :: hpl2 ->
     H.equal hl1 hl2 && H.equal hr1 hr2 && equal_hplist hpl1 hpl2

let sort_hplist =
  List.sort_uniq (fun (p1, _) (p2, _) -> H.compare p1 p2)
