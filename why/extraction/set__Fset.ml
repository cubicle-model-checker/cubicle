module S =  Set.Make (Ast.SAtom)

type 'a set = S.t

include S
