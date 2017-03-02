
module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet

module H2 : sig type t = (H.t * H.t) val compare : t -> t -> int end
module H2Map : Map.S with type key = H2.t
module H2Set : Set.S with type elt = H2.t

module HL : sig type t = H.t list val compare : t -> t -> int end
module HLMap : Map.S with type key = HL.t
module HLSet : Set.S with type elt = HL.t


val hNone : H.t

val hR : H.t
val hW : H.t
val hDirection : H.t
val hWeakVar : H.t
val hValType : H.t
val hDir : H.t
val hVar : H.t
val hVal : H.t
val hEvent : H.t

val hInt : H.t
val hProp : H.t

val hP0 : H.t
val hE0 : H.t
val hE : H.t

val hPo : H.t
val hRf : H.t
val hCo : H.t
val hFence : H.t
val hSync : H.t
val hPoLoc : H.t
val hPpo : H.t
val hSci : H.t
val hPropi : H.t

val mk_hP : int -> H.t
val mk_hE : int -> H.t
val mk_hV : H.t -> H.t
val mk_hT : H.t -> H.t

val is_param : H.t -> bool

val sort_params : 'a * 'b * (H.t * 'c) list -> 'a * 'b * 'c list

val same_dir : H.t * 'a * 'b -> H.t * 'c * 'd -> bool
val same_var : 'a * H.t * H.t list -> 'b * H.t * H.t list -> bool
val is_read : H.t * 'a * 'b -> bool
val is_write : H.t * 'a * 'b -> bool

val int_of_e : H.t -> int

val var_of_v : H.t -> string

val init_weak_env : (H.t * H.t list * H.t) list -> unit
