module S =  Set.Make (Ast.ArrayAtom)

type 'a set = S.t

open S
