

module Cores : sig

  val set_number_of_cores : int -> unit
  val compute : 
    worker:('a -> 'b) -> 
    master:('a * 'c -> 'b -> ('a * 'c) list) -> ('a * 'c) list -> unit

end
