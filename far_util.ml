open Ast
open Types

let find_pre_node t acc ncube =
  let (nl, nl') = Pre.pre_image [t] ncube in
  List.rev_append nl (List.rev_append nl' acc)
    
let compute_pre t ednf = List.fold_left (find_pre_node t) [] ednf
