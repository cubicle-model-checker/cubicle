type t = int array
(** The type of states, we allow states to be constructed from the outside by
    calling the function [new_undef_state]. *)

(* Functions for clustering *)
val diff : t -> t -> (int * (int * int)) list

val compare : t -> t -> int
val equal : t -> t -> bool

val print : string -> t -> unit

val distance : t -> t -> int
val copy : t -> t
val add_states : t -> t -> t

val count_mones : t -> int
