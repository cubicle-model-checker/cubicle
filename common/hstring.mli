
open Hashcons 

module TimeHS : Timer.S

type t = string hash_consed

val make : string -> t

val view : t -> string

val equal : t -> t -> bool

val compare : t -> t -> int

val hash : t -> int

val empty : t 

val list_assoc : t -> (t * 'a) list -> 'a

val list_mem_assoc : t -> (t * 'a) list -> bool

val list_mem : t -> t list -> bool

val list_mem_couple : t * t -> (t * t) list -> bool

val compare_list : t list -> t list -> int

val print : Format.formatter -> t -> unit

module H : Hashtbl.S with type key = t
