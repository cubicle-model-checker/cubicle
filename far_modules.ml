module Solver = Smt.Make(Options)
module Oracle = Approx.SelectedOracle
  
type result = FSafe | FUnsafe

module type SigQ = sig

  type 'a t

  exception Empty

  val create : unit -> 'a t
  val push : 'a -> 'a t -> unit
  val pop : 'a t -> 'a
end

let select_strat =
  (match Options.ic3_mode with
    | "bfs" -> (module Queue : SigQ)
    | "dfs" -> (module Stack)
    | _ -> assert false
  )

module Q : SigQ = (val (select_strat))
