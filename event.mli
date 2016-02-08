
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

val gen_po : structure -> (int * int) list

val gen_fence : structure -> (int * int) list

val gen_co : structure -> (int * int) list

val gen_co_cands : structure -> (int * int) list list

val gen_rf_cands : structure -> (int * int) list list
