
module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet

module H2 = struct
  type t = (H.t * H.t)
  let compare (s1a, s1b) (s2a, s2b) =
    let c = H.compare s1a s2a in
    if c <> 0 then c else H.compare s1b s2b
end

module H2Map = Map.Make (H2)
module H2Set = Set.Make (H2)

module HL = struct
  type t = H.t list
  let compare = H.compare_list
end

module HLMap = Map.Make (HL)
module HLSet = Set.Make (HL)



let hNone = H.make ""

let hR = H.make "_R"
let hW = H.make "_W"
let hDirection = H.make "_direction"
let hWeakVar = H.make "_weak_var"
let hValType = H.make "_val_type"
let hDir = H.make "_dir"
let hVar = H.make "_var"
let hVal = H.make "_val"
let hEvent = H.make "_event"

let hInt = H.make "int"
let hProp = H.make "prop"

let hP0 = H.make "#0"
let hE0 = H.make "_e0"
let hE = H.make "_e"

let hPo = H.make "_po"
let hRf = H.make "_rf"
let hCo = H.make "_co"
let hFence = H.make "_fence"
let hPoLoc = H.make "_po_loc"
let hPpo = H.make "_ppo"
let hSci = H.make "_sci"
let hPropi = H.make "_propi"

let hSync = H.make "_sync"

let hUniprocRW = H.make "_uniprocRW"
let hUniprocWR = H.make "_uniprocWR"

let mk_hP p = H.make ("_p" ^ (string_of_int p))
let mk_hE e = H.make ("_e" ^ (string_of_int e))
let mk_hV hv = H.make ("_V" ^ (H.view hv))
let mk_hT ht = H.make ("_t" ^ (H.view ht)) (* for event value type *)



let pl = ref [] (* event fields corresponding to array parameters *)

let is_param f = List.exists (fun (p, _) -> H.equal f p) !pl

let sort_params (d, v, vi) =
  let vi = List.sort_uniq (fun (p1, _) (p2, _) -> H.compare p1 p2) vi in
  (d, v, List.map (fun (_, i) -> i) vi)

let same_dir (d1, _, v_) (d2, _, _) = H.equal d1 d2

let same_var (_, v1, vi1) (_, v2, vi2) = H.equal v1 v2 && H.list_equal vi1 vi2

let is_read (d, _, _) = H.equal d hR

let is_write (d, _, _) = H.equal d hW



let int_of_e e =
  let e = H.view e in
  let e = String.sub e 2 (String.length e - 2) in
  int_of_string e

let var_of_v v =
  let v = H.view v in
  let v = String.sub v 2 (String.length v - 2) in
  v



module T = Smt.Type
module S = Smt.Symbol

let init_weak_env wvl =

  T.declare hDirection [hR; hW];
  T.declare hWeakVar (List.map (fun (wv, _, _) -> mk_hV wv) wvl);

  (* wts : set of all types of weak variables / maxp : max. number of params *)
  let wts, maxp = List.fold_left (fun (wts, maxp) (wv, args, ret) ->
    let nbp = List.length args in
    HSet.add ret wts, if nbp > maxp then nbp else maxp
  ) (HSet.empty, 0) wvl in

  (* wtl : list of all types of weak variable + corresponding field name *)
  let wtl = HSet.fold (fun wt wtl -> (mk_hT wt, wt) :: wtl) wts [] in
  T.declare_record hValType (List.rev wtl);

  for i = maxp downto 1 do pl := (mk_hP i, hInt) :: !pl done;
  T.declare_record hEvent
    ((hDir, hDirection) :: (hVar, hWeakVar) :: (hVal, hValType) :: !pl);

  for i = 0 to 50 do S.declare (mk_hE i) [] T.type_int done;

  let int2 = [T.type_int; T.type_int] in
  let int4 = [T.type_int; T.type_int; T.type_int; T.type_int] in

  S.declare hE int2 hEvent;
  S.declare hPo int4 T.type_prop;
  S.declare hRf int4 T.type_prop;
  S.declare hCo int4 T.type_prop;
  S.declare hFence int4 T.type_prop;
  S.declare hSync int4 T.type_prop;
  S.declare hPoLoc int4 T.type_prop;
  S.declare hPpo int4 T.type_prop;
  S.declare hSci int2 T.type_int;
  S.declare hPropi int2 T.type_int;

  S.declare hUniprocRW int2 T.type_int;
  S.declare hUniprocWR int2 T.type_int
