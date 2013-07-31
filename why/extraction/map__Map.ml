module M = Map.Make (ArrayAtom)

type ('a, 'b) map = 'b M.t


let mixfix_lblsmnrb m a b = M.add a b m

let mixfix_lbrb m a = M.find a m

let empty = M.empty
