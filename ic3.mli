open Ast

type result =
  | RSafe
  | RUnsafe

module type SigRG = sig
  val search : (unit -> unit) -> t_system -> result
end

module RG : SigRG


(* (\* Rushby graph *\) *)

(* (\* Vertices *\) *)
(* type vertice *)

(* module type SigVerticesSet = sig *)
(*   type elt = vertice *)
(*   type t *)

(*   val empty : t *)
(* end *)

(* module VerticesSet : SigVerticesSet *)


(* (\* Transitions *\) *)
(* type transition *)

(* (\* Edges *\) *)
(* type edge = { pred : vertice; *)
(* 	      trans : transition; *)
(* 	      succ : vertice} *)

(* module type SigEdgesSet = sig *)
(*   type elt = edge *)
(*   type t *)

(*   val empty : t *)
(*   val add : elt -> t -> t *)
(* end *)

(* module EdgesSet : SigEdgesSet *)

(* module type SigWorkingQueue = sig *)

(*   (\* The type of working queues containing elements of type 'a. *\) *)
(*   type 'a t  *)

(*   (\* Raised when pop or top is applied to an empty working queue. *\) *)
(*   exception Empty *)

(*   (\* Return a new working queue, initially empty. *\) *)
(*   val create : unit -> 'a t *)

(*   (\* push x s adds the element x in the working queue s. *\) *)
(*   val push : 'a -> 'a t -> unit *)

(*   (\* pop s removes and returns the first (according *)
(*      to the queue policy) element in working queue s,  *)
(*      or raises Empty if the working queue is empty. *\) *)
(*   val pop : 'a t -> 'a *)

(*   (\* Discard all elements from a working queue. *\) *)
(*   val clear : 'a t -> unit *)

(*   (\* Return a copy of the given working queue. *\) *)
(*   val copy : 'a t -> 'a t *)

(*   (\* Return true if the given working queue is empty,  *)
(*      false otherwise. *\) *)
(*   val is_empty : 'a t -> bool *)

(*   (\* Return the number of elements in a working queue. *\) *)
(*   val length : 'a t -> int *)

(*   val iter : ('a -> unit) -> 'a t -> unit *)

(* end *)

(* module WorkingQueue : SigWorkingQueue *)

(* type rushby_graph = { vertices : VerticesSet.t; *)
(* 		      edges : EdgesSet.t; *)
(* 		      root : vertice} *)
