
module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet

module H2 : sig type t = (H.t * H.t) val compare : t -> t -> int end
module H2Map : Map.S with type key = H2.t
module H2Set : Set.S with type elt = H2.t

module HEvt : sig
  type t = (H.t * H.t * H.t * H.t list)
  val compare : t -> t -> int
end
module HEvtMap : sig
  include Map.S with type key = HEvt.t
  val findp : (key -> 'a -> bool) -> 'a t -> (key * 'a)
end
module HEvtSet : Set.S with type elt = HEvt.t

module HVar : sig
  type t = (H.t * H.t list)
  val compare : t -> t -> int
end
module HVarMap : sig
  include Map.S with type key = HVar.t
  val findp : (key -> 'a -> bool) -> 'a t -> (key * 'a)
end
module HVarSet : Set.S with type elt = HVar.t

module HL : sig type t = H.t list val compare : t -> t -> int end
module HLMap : Map.S with type key = HL.t
module HLSet : Set.S with type elt = HL.t


val hNone : H.t

val hR : H.t
val hW : H.t
val hDirection : H.t
val hWeakVar : H.t
val hValType : H.t
val hThr : H.t
val hDir : H.t
val hVar : H.t
val hVal : H.t
val hEvent : H.t

val hInt : H.t
val hProp : H.t

val hP0 : H.t
val hE0 : H.t
val hE : H.t

(* val hPo : H.t *)
(* val hRf : H.t *)
(* val hCo : H.t *)
(* val hFr : H.t *)
val hFence : H.t
val hSync : H.t
(* val hPoLoc : H.t *)
(* val hPpo : H.t *)
val hGhb : H.t

val mk_hP : int -> H.t
val mk_hE : int -> H.t
val mk_hV : H.t -> H.t
val mk_hT : H.t -> H.t

val is_param : H.t -> bool

val sort_params : 'a * 'b * 'c * (H.t * 'd) list -> 'a * 'b * 'c * 'd list

val same_proc : H.t * 'a * 'b * 'c -> H.t * 'd * 'e * 'f -> bool
val same_dir : 'a * H.t * 'b * 'c -> 'd * H.t * 'e * 'f -> bool
val same_var : 'a * 'b * H.t * H.t list -> 'c * 'd * H.t * H.t list -> bool
val is_read : 'a * H.t * 'b * 'c -> bool
val is_write : 'a * H.t * 'b * 'c -> bool

val int_of_e : H.t -> int

val var_of_v : H.t -> string

val is_weak : H.t -> bool

val weak_type : H.t -> H.t list * HSet.elt
                 
val init_weak_env : (H.t * H.t list * H.t) list -> unit

val cartesian_product : ('a -> 'a -> 'a) -> 'a list -> 'a list -> 'a list
val cartesian_product_h2m :'a H2Map.t list -> 'a H2Map.t list -> 'a H2Map.t list
