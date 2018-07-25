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
  type t = (H.t * H.t * H.t * H.t)
  let compare (s1d, s1p, s1q, s1c) (s2d, s2p, s2q, s2c) =
    let c = H.compare s1d s2d in if c <> 0 then c else
    let c = H.compare s1p s2p in if c <> 0 then c else
    let c = H.compare s1q s2q in if c <> 0 then c else
    (* H.compare s1c s2c in *)
    Pervasives.compare (H.view s1c) (H.view s2c)
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

module HChan = struct
  type t = H.t
  let compare s1c s2c =
    (* H.compare s1c s2c in *)
    Pervasives.compare (H.view s1c) (H.view s2c)
end
module HChanMap = struct
  include Map.Make (HChan)
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
module HChanSet = Set.Make (HChan)

module HL = struct
  type t = H.t list
  let compare = H.compare_list
end
module HLMap = Map.Make (HL)
module HLSet = Set.Make (HL)



let hNone = H.make ""

let hE0 = H.make "_e0"

let hR = H.make "_R"
let hS = H.make "_S"
let hDirection = H.make "_direction"
let hChannel = H.make "_channel"
let hDir = H.make "_e_dir"
let hThr = H.make "_e_thr"
let hPeer = H.make "_e_peer"
let hChan = H.make "_e_chan"

let hSync = H.make "_sync"
let hGhb = H.make "_ghb"

let mk_hE e = H.make ("_e" ^ (string_of_int e)) (* event id *)
let mk_hC hc = H.make ("_C" ^ (H.view hc)) (* chan *)
let mk_hVal ht = H.make ("_e_val_" ^ (H.view ht)) (* value / type *)



let channels = HTbl.create 17

let is_chan = HTbl.mem channels

let chan_type = HTbl.find channels



let changrps = ref []



let is_event a =
  let a = H.view a in
  if String.length a < 3 then false else
  String.sub a 0 3 = "_e_"

let is_value a =
  let a = H.view a in
  if String.length a < 7 then false else
  String.sub a 0 7 = "_e_val_"

let is_rel a = a = hSync || a = hGhb

let same_dir (d1, _, _, _) (d2, _, _, _) = H.equal d1 d2

let same_thr (_, p1, _, _) (_, p2, _, _) = H.equal p1 p2

let same_peer (_, _, q1, _) (_, _, q2, _) = H.equal q1 q2

let same_chan (_, _, _, c1) (_, _, _, c2) = H.equal c1 c2

let same_group (_, _, _, c1) (_, _, _, c2) =
  List.exists (fun g -> HSet.mem c1 g && HSet.mem c2 g) !changrps

let echan_type (_, _, _, c) = fst (HTbl.find channels c)

let no_peer (_, _, q, _) = H.equal q hNone

let no_chan (_, _, _, c) = H.equal c hNone

let is_recv (d, _, _, _) = H.equal d hR

let is_send (d, _, _, _) = H.equal d hS



let int_of_e e =
  let e = H.view e in
  let e = String.sub e 2 (String.length e - 2) in
  int_of_string e

let var_of_v v =
  let v = H.view v in
  let v = String.sub v 2 (String.length v - 2) in
  v



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

(* let init_env cl = *)
let init_env (cl:(H.t * Types.chantype * Smt.Type.t) list)
             (grps:(H.t list list)) : unit =

  List.iter (fun (c, ct, vt) ->
    HTbl.replace channels c (ct, vt);
    HTbl.replace channels (mk_hC c) (ct, vt);
  ) cl;

  changrps := List.map (fun cl ->
    List.fold_left (fun g c -> HSet.add (mk_hC c) g) HSet.empty cl
  ) grps;

  T.declare hDirection [hR; hS];
  T.declare hChannel (List.map (fun (c, _, _) -> mk_hC c) cl);

  (* cvts : set of all channel value types *)
  let cvts = List.fold_left (fun cvts (c, ct, vt) ->
    HSet.add vt cvts
  ) HSet.empty cl in

  (* Make value fields *)
  (* cvtl : list of all channel value types + corresponding field name *)
  let cvtl = HSet.fold (fun vt cvtl -> (mk_hVal vt, vt) :: cvtl) cvts [] in

  (* should adjust automatically *)
  for i = 0 to 100 do S.declare (mk_hE i) [] T.type_int done;

  S.declare hThr [T.type_int] T.type_proc;
  S.declare hPeer [T.type_int] T.type_proc;
  S.declare hDir [T.type_int] hDirection;
  S.declare hChan [T.type_int] hChannel;
  List.iter (fun (hVal, vt) -> S.declare hVal [T.type_int] vt) cvtl;

  S.declare hGhb [T.type_int; T.type_int] T.type_bool; (* to remove *)
