
module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet

module H2 : sig type t = (H.t * H.t) val compare : t -> t -> int end
module H2Map : Map.S with type key = H2.t
module H2Set : Set.S with type elt = H2.t

module HEvt : sig
  type t = (H.t * H.t * H.t * H.t)
  val compare : t -> t -> int
end
module HEvtMap : sig
  include Map.S with type key = HEvt.t
  val findp : (key -> 'a -> bool) -> 'a t -> (key * 'a)
end
module HEvtSet : Set.S with type elt = HEvt.t

module HChan : sig
  type t = H.t
  val compare : t -> t -> int
end
module HChanMap : sig
  include Map.S with type key = HChan.t
  val findp : (key -> 'a -> bool) -> 'a t -> (key * 'a)
end
module HChanSet : Set.S with type elt = HChan.t

module HL : sig type t = H.t list val compare : t -> t -> int end
module HLMap : Map.S with type key = HL.t
module HLSet : Set.S with type elt = HL.t


val hNone : H.t

val hE0 : H.t

val hR : H.t
val hS : H.t
val hDirection : H.t
val hChannel : H.t
val hDir : H.t
val hThr : H.t
val hPeer : H.t
val hChan : H.t

val hSync : H.t
val hGhb : H.t

val mk_hE : int -> H.t
val mk_hC : H.t -> H.t
val mk_hVal : H.t -> H.t

val is_event : H.t -> bool
val is_value : H.t -> bool
val is_rel : H.t -> bool

val same_dir : H.t * 'a * 'b * 'c -> H.t * 'd * 'e * 'f -> bool
val same_thr : 'a * H.t * 'b * 'c -> 'd * H.t * 'e * 'f -> bool
val same_peer : 'a * 'b * H.t * 'c -> 'd * 'e * H.t * 'f -> bool
val same_chan : 'a * 'b * 'c * H.t -> 'd * 'e * 'f * H.t -> bool
val no_chan : 'a * 'b * 'c * H.t -> bool
val is_recv : H.t * 'a * 'b * 'c -> bool
val is_send : H.t * 'a * 'b * 'c -> bool

val int_of_e : H.t -> int

val var_of_v : H.t -> string

val is_chan : H.t -> bool

val chan_type : H.t -> Types.chantype * Smt.Type.t

val init_env : (H.t * Types.chantype * Smt.Type.t) list -> unit


val cartesian_product : ('a -> 'a -> 'a) -> 'a list -> 'a list -> 'a list
(* val cartesian_product_h2m :'a H2Map.t list -> 'a H2Map.t list -> 'a H2Map.t list *)

