
type dir = ERead | EWrite

type t = {
    uid : int;
    tid : Variable.t;
    dir : dir;
    var : Hstring.t * Variable.t list; }

module IntMap : Map.S with type key = int

type structure = t list IntMap.t

val empty_struct : structure

val make : Hstring.t -> (Hstring.t * Variable.t list) -> dir -> t

val name : t -> string

val print : Format.formatter -> t -> unit

val print_rd : Format.formatter ->
	       (Hstring.t * Hstring.t * Variable.t list) -> unit

val print_decls : Format.formatter -> bool ->
		  ('a * 'b * 'c) Hstring.H.t -> structure list -> unit

val print_rels : Format.formatter -> structure list -> unit
