
module H = Hstring

(* val compare_hpair : (H.t * H.t) -> (H.t * H.t) -> int *)
val compare_hplist : (H.t * H.t) list -> (H.t * H.t) list -> int

val equal_hplist : (H.t * H.t) list -> (H.t * H.t) list -> bool

val sort_hplist : (H.t * H.t) list -> (H.t * H.t) list
