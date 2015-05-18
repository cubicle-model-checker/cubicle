type result = RSafe | RUnsafe

module type SigV =
  sig
    type t
    type ucnf
    type ednf
    type res_ref = 
      | Bad_Parent
      | Covered of t 
      | Extrapolated of t

    val create_good : (Variable.t list * Types.SAtom.t) list -> ucnf
    val create_bad : (Variable.t list * Types.SAtom.t) list -> ednf
    val create : ?creation:(t * Ast.transition * t) ->ucnf -> ednf -> t
    
    val delete_parent : t -> t * Ast.transition -> bool
    val add_parent : t -> t * Ast.transition -> unit
    val get_parents : t -> (t * Ast.transition) list
    val update_bad_from : t -> Ast.transition -> t -> unit
    val update_good_from : t -> t -> unit
   
    (* Signature in case we want to make a Hashtbl *)
    val hash : t -> int
    val equal : t -> t -> bool

    (* Signature in case we want to make a Map or a Set *)
    val compare : t -> t -> int
    
    val print_vertice : Format.formatter -> t -> unit
    val save_vertice : Format.formatter -> t -> unit

    val print_id : Format.formatter -> t -> unit
    val save_id : Format.formatter -> t -> unit

    val print_vednf : Format.formatter -> t -> unit
    
    val add_node_dot : t -> unit
    val add_node_step : t -> string -> unit
    val add_parents_dot : t -> unit
    val add_parents_step : t -> unit
    val add_relation_step :
      ?color:string -> ?style:string -> t -> t -> Ast.transition -> unit

    val expand : t -> Ast.transition list -> Ast.transition list
    val refine : t -> t -> Ast.transition -> t list -> res_ref
    val is_bad : t -> bool
  end

module type SigQ =
  sig
    type 'a t
    exception Empty
    val create : unit -> 'a t
    val push : 'a -> 'a t -> unit
    val pop : 'a t -> 'a
  end

module Make :
  functor (Q : SigQ) ->
    functor (V : SigV) ->
      sig
        type v = V.t
        type q = V.t Q.t
        module G : Map.S
        
        exception Unsafe of V.t list G.t * V.t
        exception Safe of V.t list G.t
        
        val search : (unit -> 'a) -> Ast.t_system -> result
      end

module type SigRG = sig 
  val search : (unit -> unit) -> Ast.t_system -> result
end

module Vertice : SigV

module RG :
  sig
    type v = Vertice.t
    type q = Vertice.t Queue.t
    module G : Map.S
    
    exception Unsafe of Vertice.t list G.t * Vertice.t
    exception Safe of Vertice.t list G.t
    
    val search : (unit -> 'a) -> Ast.t_system -> result
  end
