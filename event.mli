
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

val int_of_tid : t -> int

val print : Format.formatter -> t -> unit

val print_rd : Format.formatter ->
	       (Hstring.t * Hstring.t * Variable.t list) -> unit

val gen_po : structure -> (int * int) list

val print_decls : Format.formatter -> bool ->
		  ('a * 'b * 'c) Hstring.H.t -> structure list -> unit

val print_goal : Format.formatter -> bool -> structure list -> unit
