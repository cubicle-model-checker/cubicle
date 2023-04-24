module IntMap     = Map.Make(struct type t = int let compare : int -> int -> int = Int.compare end) 
module StringMap  = Map.Make(struct type t = string let compare : string -> string -> int = String.compare end)
