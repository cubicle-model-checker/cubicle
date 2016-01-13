
type dir = ERead | EWrite

type t = {
    uid : int;
    tid : Hstring.t; (* Variablt.t *)
    dir : dir;
    var : Hstring.t * Hstring.t list; (* Variablt.t *)
  }

module IntMap : Map.S with type key = int

type structure = t list IntMap.t

val empty_struct : structure

val make : Hstring.t -> (Hstring.t * Hstring.t list) -> dir -> t

val print_rd : Format.formatter -> (Hstring.t * Hstring.t
	       * Hstring.t list) -> unit

val print_evtval : Format.formatter -> t -> unit

val event_name : t -> string

val smt_var_name : Hstring.t -> string

val print_event_decls : Format.formatter -> t list -> unit

val print_events_po : Format.formatter -> structure -> unit

val print_acyclic_relations : Format.formatter -> t list -> unit

val unique_events : structure list -> t list

val axiom : bool -> string
