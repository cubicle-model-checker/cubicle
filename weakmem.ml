
module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet
module HTbl = Hstring.H

module H2 = struct
  type t = (H.t * H.t)
  let compare (s1a, s1b) (s2a, s2b) =
    let c = H.compare s1a s2a in
    if c <> 0 then c else H.compare s1b s2b
end
module H2Map = Map.Make (H2)
module H2Set = Set.Make (H2)

module HEvt = struct
  type t = (H.t * H.t * H.t * H.t list)
  let compare (s1p, s1d, s1v, s1vi) (s2p, s2d, s2v, s2vi) =
    let c = H.compare s1p s2p in
    if c <> 0 then c else
    let c = H.compare s1d s2d in
    if c <> 0 then c else
    (* let c = H.compare s1v s2v in *)
    let c = Pervasives.compare (H.view s1v) (H.view s2v) in
    if c <> 0 then c else
    H.compare_list s1vi s2vi
end
module HEvtMap = struct
  include Map.Make (HEvt)
  exception Stop
  let findp p m =
    let res = ref None in
    begin try iter (fun k v -> if p k v then begin
                    res := Some (k, v); raise Stop end) m
          with Stop -> () end;
    match !res with
    | Some (k, v) -> k, v
    | _ -> raise Not_found
end
module HEvtSet = Set.Make (HEvt)

module HVar = struct
  type t = (H.t * H.t list)
  let compare (s1v, s1vi) (s2v, s2vi) =
    (* let c = H.compare s1v s2v in *)
    let c = Pervasives.compare (H.view s1v) (H.view s2v) in
    if c <> 0 then c else
    H.compare_list s1vi s2vi
end
module HVarMap = struct
  include Map.Make (HVar)
  exception Stop
  let findp p m =
    let res = ref None in
    begin try iter (fun k v -> if p k v then begin
                    res := Some (k, v); raise Stop end) m
          with Stop -> () end;
    match !res with
    | Some (k, v) -> k, v
    | _ -> raise Not_found
end
module HVarSet = Set.Make (HVar)

module HL = struct
  type t = H.t list
  let compare = H.compare_list
end
module HLMap = Map.Make (HL)
module HLSet = Set.Make (HL)



let hNone = H.make ""

let hE0 = H.make "_e0"
(* let hP0 = H.make "#0" *)

let hR = H.make "_R"
let hW = H.make "_W"
let hDirection = H.make "_direction"
let hWeakVar = H.make "_weak_var"
let hThr = H.make "_e_thr"
let hDir = H.make "_e_dir"
let hVar = H.make "_e_var"

let hFence = H.make "_fence"
let hSync = H.make "_sync"
let hGhb = H.make "_ghb"

let mk_hE e = H.make ("_e" ^ (string_of_int e)) (* event id *)
let mk_hV hv = H.make ("_V" ^ (H.view hv)) (* var *)
let mk_hArg p = H.make ("_e_p" ^ (string_of_int p)) (* arguments *)
let mk_hVal ht = H.make ("_e_val_" ^ (H.view ht)) (* value / type *)




let is_event a =
  let a = H.view a in
  if String.length a < 3 then false else
  let a = String.sub a 0 3 in
  a = "_e_"

let wtl = ref [] (* arrays corresponding to event values *)

(* let is_value a = List.exists (fun (wt, _) -> H.equal a wt) !wtl *)
let is_value a =
  let a = H.view a in
  if String.length a < 7 then false else
  let a = String.sub a 0 7 in
  a = "_e_val_"

let pl = ref [] (* arrays corresponding to event array parameters *)

(* let is_param a = List.exists (fun (p, _) -> H.equal a p) !pl *)
let is_param a =
  let a = H.view a in
  if String.length a < 4 then false else
  let a = String.sub a 0 4 in
  a = "_e_p"

let sort_params (p, d, v, vi) =
  let vi = List.sort_uniq (fun (p1, _) (p2, _) -> H.compare p1 p2) vi in
  (p, d, v, List.map (fun (_, i) -> i) vi)

let same_proc (p1, _, _, _) (p2, _, _, _) = H.equal p1 p2

let same_dir (_, d1, _, _) (_, d2, _, _) = H.equal d1 d2

let same_var (_, _, v1, vi1) (_, _, v2, vi2) =
  H.equal v1 v2 && H.list_equal vi1 vi2

let no_var (_, _, v, _) = H.equal v hNone

let is_read (_, d, _, _) = H.equal d hR

let is_write (_, d, _, _) = H.equal d hW



let int_of_e e =
  let e = H.view e in
  let e = String.sub e 2 (String.length e - 2) in
  int_of_string e

let var_of_v v =
  let v = H.view v in
  let v = String.sub v 2 (String.length v - 2) in
  v



let weak_vars = HTbl.create 17

let is_weak = HTbl.mem weak_vars

let weak_type = HTbl.find weak_vars


(* could extend op with Some/None to conditionally compute product *)
let cartesian_product op l1 l2 =
  if l1 = [] then l2 else if l2 = [] then l1 else
  List.fold_left (fun rl e1 ->
    List.fold_left (fun rl e2 ->
      (op e1 e2) :: rl
    ) rl l2
  ) [] l1

(* let cartesian_product_h2m l1 l2 = *)
(*   cartesian_product (H2Map.union (fun k v1 v2 -> *)
(*     failwith "Weakmem.cartesian_product : duplicate")) l1 l2 *)



module T = Smt.Type
module S = Smt.Symbol

let init_weak_env wvl =

  let hInt = H.make "int" in

  List.iter (fun (wv, args, ret) ->
    HTbl.replace weak_vars wv (args, ret);
    HTbl.replace weak_vars (mk_hV wv) (args, ret);
  ) wvl;
  
  T.declare hDirection [hR; hW];
  T.declare hWeakVar (List.map (fun (wv, _, _) -> mk_hV wv) wvl);

  (* wts : set of all types of weak variables / maxp : max. number of params *)
  let wts, maxp = List.fold_left (fun (wts, maxp) (wv, args, ret) ->
    let nbp = List.length args in
    HSet.add ret wts, if nbp > maxp then nbp else maxp
  ) (HSet.empty, 0) wvl in

  (* Make value fields *)
  (* wtl : list of all types of weak variable + corresponding field name *)
  wtl := HSet.fold (fun wt wtl -> (mk_hVal wt, wt) :: wtl) wts [];

  (* Make argument fields *)
  for i = maxp downto 1 do pl := (mk_hArg i, hInt) :: !pl done;

  (* should adjust automatically *)
  for i = 0 to 100 do S.declare (mk_hE i) [] T.type_int done;

  let int1 = [T.type_int] in
  let int2 = [T.type_int; T.type_int] in

  (* S.declare hP0 [] T.type_proc; *)

  S.declare hThr int1 T.type_proc;
  S.declare hDir int1 hDirection;
  S.declare hVar int1 hWeakVar;
  List.iter (fun (hArg, t) -> S.declare hArg int1 t) !pl;
  List.iter (fun (hVal, t) -> S.declare hVal int1 t) !wtl;

  S.declare hFence int2 T.type_prop;
  S.declare hSync int2 T.type_prop;
  S.declare hGhb int2 T.type_prop
