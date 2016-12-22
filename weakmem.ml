
module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet

module H3 = struct
  type t = (H.t * H.t * H.t)
  let compare (s1a, s1b, s1c) (s2a, s2b, s2c) =
    let c = H.compare s1a s2a in if c <> 0 then c else
    let c = H.compare s1b s2b in if c <> 0 then c else
    H.compare s1c s2c
end

module H3Map = Map.Make (H3)



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
let hE = H.make "_e"
let hE1 = H.make "_e1"
let hS1 = H.make "_s1"

let hF = H.make "_f"

let hPo = H.make "_po"
let hRf = H.make "_rf"
let hCo = H.make "_co"
let hFence = H.make "_fence"
let hPoLoc = H.make "_po_loc"
let hPpo = H.make "_ppo"
let hSci = H.make "_sci"
let hPropi = H.make "_propi"

let mk_hE e = H.make ("_e" ^ (string_of_int e))
let mk_hS s = H.make ("_s" ^ (string_of_int s))
let mk_hP p = H.make ("_p" ^ (string_of_int p))
let mk_hV hv = H.make ("_V" ^ (H.view hv))
let mk_hT ht = H.make ("_t" ^ (H.view ht))



let pl = ref []

let is_param f =
  List.exists (fun (p, _) -> H.equal f p) !pl

let same_var (_, v1, vi1) (_, v2, vi2) =
  H.equal v1 v2 && H.list_equal vi1 vi2



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
  T.declare hWeakVar (List.map (fun (v, _, _) -> mk_hV v) wvl);

  (* wts : set of all types of weak variables / maxp : max. number of params *)
  let wts, maxp = List.fold_left (fun (wts, maxp) (wv, args, ret) ->
    let nbp = List.length args in
    HSet.add ret wts, if nbp > maxp then nbp else maxp
  ) (HSet.empty, 0) wvl in

  (* wtl : list of all types of weak variable + corresponding field name *)
  let wtl = HSet.fold (fun wt wtl -> (mk_hT wt, wt) :: wtl) wts [] in
  T.declare_record hValType wtl;

  for i = maxp downto 1 do pl := (mk_hP i, hInt) :: !pl done;
  T.declare_record hEvent
    ((hDir, hDirection) :: (hVar, hWeakVar) :: (hVal, hValType) :: !pl);

  S.declare hE [T.type_proc; T.type_int; T.type_int] hEvent;

  for i = 1 to 50 do S.declare (mk_hE i) [] T.type_int done;
  for i = 1 to 10 do S.declare (mk_hS i) [] T.type_int done;

  let int2 = [T.type_int; T.type_int] in
  let int4 = [T.type_int; T.type_int; T.type_int; T.type_int] in
  let int6 = [T.type_int; T.type_int; T.type_int;
	      T.type_int; T.type_int; T.type_int] in

  S.declare hPo int4 T.type_prop;
  S.declare hRf int6 T.type_prop;
  S.declare hCo int6 T.type_prop;
  S.declare hFence int4 T.type_prop;
  S.declare hPoLoc int6 T.type_prop;
  S.declare hPpo int6 T.type_prop;
  S.declare hSci int2 T.type_int;
  S.declare hPropi int2 T.type_int

  (* let int3 = [T.type_int; T.type_int; T.type_int] in *)
  (* S.declare (H.make "_coi") int3 T.type_int *)
