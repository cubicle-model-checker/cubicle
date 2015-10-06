type result = 
  RSafe  | RUnsafe

module type SigQ =
  sig
    type 'a t
    exception Empty
    val create : unit -> 'a t
    val push : 'a -> 'a t -> unit
    val pop : 'a t -> 'a
  end

val search : (unit -> 'a) -> Ast.t_system -> result
