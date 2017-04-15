
open Weakmem
open Types
open Util


       
module RInt = struct
  type t = int
  let compare x y = - (Pervasives.compare x y)
end

module RIntMap = Map.Make (RInt)



