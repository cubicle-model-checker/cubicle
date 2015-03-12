
exception Empty
(*exception Not_found*)

type 'a t

val empty : 'a t

val is_empty : 'a t -> bool

val push : 'a -> 'a t -> 'a t

val pop : 'a t -> 'a * 'a t

val iter : ('a -> unit) -> 'a t -> unit (* iter from head to tail *)

val rev_iter : ('a -> unit) -> 'a t -> unit (* iter from tail to head *)

val fold_left : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b (* fold from head to tail*)

val fold_right : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b (*fold from tail to head*)

val for_all : ('a -> bool) -> 'a t -> bool

val exists : ('a -> bool) -> 'a t -> bool

val find : ('a -> bool) -> 'a t -> 'a (* find from head *)

val rev_find : ('a -> bool) -> 'a t -> 'a (* find from tail *)
