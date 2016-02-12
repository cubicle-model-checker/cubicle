
module H = Hstring
module HMap = Hstring.HMap
module T = Smt.Term
module F = Smt.Formula



val init_weak_env : H.t list -> unit



val make_event : int HMap.t * Types.term list HMap.t * Types.Atom.t list ->
		 string -> HMap.key -> Hstring.t -> 'a ->
		 (int HMap.t * Types.term list HMap.t * Types.Atom.t list) * Types.term
val event_of_term : int HMap.t * Types.term list HMap.t * Types.Atom.t list ->
		    Types.term ->
		  (int HMap.t * Types.term list HMap.t * Types.Atom.t list) * Types.term
val events_of_a : int HMap.t * Types.term list HMap.t * Types.Atom.t list ->
		  Types.Atom.t ->
		(int HMap.t * Types.term list HMap.t * Types.Atom.t list) * Types.Atom.t
val events_of_satom : Types.SAtom.t -> Types.SAtom.t



val merge_ord : 'a list HMap.t -> 'a list HMap.t -> 'a list HMap.t
val merge_evts : 'a HMap.t HMap.t -> 'a HMap.t HMap.t -> 'a HMap.t HMap.t



val split_order : Types.Atom.t -> Types.Atom.t option * (H.t * H.t list) option
val split_order_array : Types.SAtom.elt array -> Types.SAtom.t * H.t list HMap.t
val split_order_set : Types.SAtom.t -> Types.SAtom.t * H.t list HMap.t
val get_events : Types.SAtom.t -> (H.t * H.t) HMap.t HMap.t



val gen_po : H.t list HMap.t -> (H.t * H.t * H.t * H.t) list
val gen_fence : (H.t * H.t) HMap.t HMap.t -> H.t list HMap.t ->
		(H.t * H.t * H.t * H.t) list
val gen_co : (H.t * H.t) HMap.t HMap.t -> H.t list HMap.t ->
	     (H.t * H.t * H.t * H.t) list
val gen_co_cands : (H.t * H.t) HMap.t HMap.t -> (H.t * H.t * H.t * H.t) list list
val gen_rf_cands : (H.t * H.t) HMap.t HMap.t -> (H.t * H.t * H.t * H.t) list list



val make_pred : string -> H.t * H.t * H.t * H.t -> bool -> F.t
val make_acyclic_rel : H.t * H.t -> F.t list
val make_rel : string -> (H.t * H.t * H.t * H.t) list -> F.t list
val make_cands : string -> (H.t * H.t * H.t * H.t) list list -> F.t list
val make_orders : ?fp:bool -> (H.t * H.t) HMap.t HMap.t -> H.t list HMap.t -> F.t



(*
type dir = ERead | EWrite

type t = {
    uid : int;
    tid : Variable.t;
    dir : dir;
    var : Hstring.t * Variable.t list; }

module IntMap : Map.S with type key = int

type structure = {
    events : t IntMap.t;
    po_f : int list IntMap.t; }

val empty_struct : structure

val make : int -> Hstring.t -> dir -> (Hstring.t * Variable.t list) -> t

val name : t -> string

val int_of_tid : Variable.t -> int

val print : Format.formatter -> t -> unit

val print_rd : Format.formatter ->
	       (Hstring.t * Hstring.t * Variable.t list) -> unit

val es_permutations : structure -> structure -> (int * int) list list

val es_apply_subst : (int * int) list -> structure -> structure

val es_add_events : structure -> t list -> structure

val es_add_events_full : structure -> t list -> structure

val es_add_fences : structure -> Variable.t list -> structure

val gen_po : structure -> (t * t) list

val gen_fence : structure -> (t * t) list

val gen_co : structure -> (t * t) list

val gen_co_cands : structure -> (t * t) list list

val gen_rf_cands : structure -> (t * t) list list

 *)
