
module H = Hstring
module HMap = Hstring.HMap
module HSet = Hstring.HSet

module H3 : sig type t = (H.t * H.t * H.t) end
module H3Map : Map.S with type key = H3.t



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
val hE : H.t
val hE1 : H.t
val hS1 : H.t

val hF : H.t

val hPo : H.t
val hRf : H.t
val hCo : H.t
val hFence : H.t
val hPoLoc : H.t
val hPpo : H.t
val hSci : H.t
val hProp : H.t

val mk_hE : int -> H.t
val mk_hS : int -> H.t
val mk_hP : int -> H.t
val mk_hV : H.t -> H.t
val mk_hT : H.t -> H.t

val is_param : H.t -> bool

val same_var : 'a * H.t * H.t list -> 'b * H.t * H.t list -> bool

val int_of_e : H.t -> int

val var_of_v : H.t -> string

val init_weak_env : (H.t * H.t list * H.t) list -> unit
