type t = { x : int; y : int }

let add a b = { x = a.x + b.x; y = a.y + b.y }
let sub a b = { x = a.x - b.x; y = a.y - b.y }

let mult k a = { x = k* a.x; y = k* a.y }
let div  k a = { x = a.x /k; y = a.y /k}

let dot a b     = a.x * b.x + a.y * b.y
let norm a      = int_of_float (sqrt (float_of_int (dot a a)))
let normalize a = div (norm a) a
let setsize   k a = div (norm a) (mult k a)
let pp a = Format.printf "(%d, %d)" a.x a.y

let orth v = [| { x = v.y; y = -v.x }  ; {x = -v.y; y=v.x}|]

let distance a b = Int.abs (a.x - b.x) + Int.abs (a.y - b.y)

let zero = { x = 0; y = 0 }
