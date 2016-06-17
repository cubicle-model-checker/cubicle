
module H = Hstring
module HMap = Hstring.HMap
module T = Smt.Term
module F = Smt.Formula



module HS3 : sig
  type t = (H.t * H.t * H.t)
end

module H3Map : Map.S with type key = HS3.t

(*module VI : sig
  type t = (H.t * (H.t list))
end

module VIMap : Map.S with type key = VI.t*)



val hNone : H.t
val hP0 : H.t
val hR : H.t
val hW : H.t
val hDirection : H.t
val hWeakVar : H.t
val hV : H.t
val hParam : H.t
val hVarParam : H.t
val hValType : H.t
val hDir : H.t
val hVar : H.t
val hPar : H.t
val hVal : H.t
val hEvent : H.t
val hInt : H.t
val hProp : H.t
val hO : H.t
val hF : H.t
val hE : H.t
val hPo : H.t
val hRf : H.t
val hCo : H.t
val hFence : H.t
val hCoUProp : H.t
val hPoLocUCom : H.t



val init_weak_env : (H.t * H.t list * H.t) list -> unit



val make_init_write :
  H.t * Variable.t list ->
  (H.t * H.t * H.t) * Types.term * Types.SAtom.t

val events_of_satom : Types.SAtom.t -> Types.SAtom.t




val split_events_orders_array :
  Types.SAtom.elt array ->
  Types.SAtom.t *
    (H.t * H.t * (H.t * H.t) list) HMap.t HMap.t HMap.t *
    H.t list HMap.t

val split_events_orders_set :
  Types.SAtom.t ->
  Types.SAtom.t *
    (H.t * H.t * (H.t * H.t) list) HMap.t HMap.t HMap.t *
    H.t list HMap.t



val relevant_reads :
  ('a * H.t * H.t list * Types.term) list ->
  Types.SAtom.t ->
  (H.t * H.t * (H.t * H.t) list * bool * Types.op_comp * Types.Term.t) H3Map.t
    
val relevant_reads_by_write :
  ('a * Hstring.t * H.t list * Types.term) list ->
  ('b * H.t * ('c * H.t) list * bool * Types.op_comp * Types.term) H3Map.t ->
  (('a * Hstring.t * H.t list * Types.term) *
     (H3Map.key * ('b * H.t * ('c * H.t) list *
		   bool * Types.op_comp * Types.term)) list) list

(*  ('a * H.t * H.t list * Types.term) list ->
  ('c * H.t * ('d * H.t) list * 'e * 'f * 'g) H3Map.t ->
  (('a * H.t * H.t list * 'b) *
     (H3Map.key * ('c * H.t * ('d * H.t) list * 'e * 'f * 'g)) list) list*)

val read_combinations_by_write : ('a * 'b list) list -> ('a * 'b list list) list
val all_permutations : ('a * 'b list) list -> ('a * 'b) list list
		       
val unsatisfied_reads : Types.SAtom.t -> (H.t * Hstring.t list) H3Map.t



val merge_ord : 'a list HMap.t -> 'a list HMap.t -> 'a list HMap.t
val merge_evts : 'a HMap.t HMap.t -> 'a HMap.t HMap.t -> 'a HMap.t HMap.t



val make_orders :
  ?fp:bool ->
  (H.t * H.t * (H.t * H.t) list) HMap.t HMap.t HMap.t ->
  H.t list HMap.t ->
  F.t



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
