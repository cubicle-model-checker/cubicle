
module H = Hstring
module HMap = Hstring.HMap
module T = Smt.Term
module F = Smt.Formula



module HS3 : sig
  type t = (H.t * H.t * H.t)
end

module H3Map : Map.S with type key = HS3.t



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


val split_event :
  Types.Atom.t ->
  (H.t * H.t * (Hstring.t * Hstring.t) list *
     (bool * Types.op_comp * Types.Term.t) list) H3Map.t ->
  (H.t * H.t * (Hstring.t * Hstring.t) list *
     (bool * Types.op_comp * Types.Term.t) list) H3Map.t
	

val make_read_write_combinations:
  (H.t * H.t * H.t list * Types.term) list ->
  Types.SAtom.t ->
   ((H.t * H.t * H.t list * Types.term) *
    ((H.t * H.t * H.t) *
     (H.t * H.t * (Hstring.t * H.t) list * (bool * Types.op_comp * Types.Term.t) list)
    ) list
   ) list list
		       
val unsatisfied_reads : Types.SAtom.t -> (H.t * Hstring.t list) H3Map.t





val make_orders :
  ?fp:bool ->
  (H.t * H.t * (H.t * H.t) list) HMap.t HMap.t HMap.t ->
  H.t list HMap.t ->
  F.t
