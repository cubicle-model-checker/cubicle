
module H = Hstring
module HMap = Hstring.HMap
module T = Smt.Term
module F = Smt.Formula



val init_weak_env : H.t list -> unit



val writes_of_init : Types.SAtom.t list -> Types.SAtom.t list
val events_of_satom : Types.SAtom.t -> Types.SAtom.t



val split_events_orders_array : Types.SAtom.elt array ->
				Types.SAtom.t * (Hstring.t * Hstring.t) HMap.t HMap.t *
				  Hstring.t list HMap.t
val split_events_orders_set : Types.SAtom.t ->
			      Types.SAtom.t * (Hstring.t * Hstring.t) HMap.t HMap.t *
			        Hstring.t list HMap.t



val merge_ord : 'a list HMap.t -> 'a list HMap.t -> 'a list HMap.t
val merge_evts : 'a HMap.t HMap.t -> 'a HMap.t HMap.t -> 'a HMap.t HMap.t



val make_orders : ?fp:bool -> (H.t * H.t) HMap.t HMap.t -> H.t list HMap.t -> F.t



(*

val print : Format.formatter -> t -> unit

val print_rd : Format.formatter ->
	       (Hstring.t * Hstring.t * Variable.t list) -> unit

val es_permutations : structure -> structure -> (int * int) list list

val es_apply_subst : (int * int) list -> structure -> structure

val es_add_events : structure -> t list -> structure

val es_add_events_full : structure -> t list -> structure

val es_add_fences : structure -> Variable.t list -> structure

 *)
