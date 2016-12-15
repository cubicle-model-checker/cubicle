
module H = Hstring

let compare_htriple (x1,y1,z1) (x2,y2,z2) =
  let c = H.compare x1 x2 in if c <> 0 then c else
    let c = H.compare y1 y2 in if c <> 0 then c else
      H.compare z1 z2

let rec compare_htlist l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | x :: r1, y :: r2 ->
     let c = compare_htriple x y in
     if c <> 0 then c else
       compare_htlist r1 r2
