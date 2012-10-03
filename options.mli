(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

type mode = 
  | Dfs | DfsL | DfsH | DfsHL 
  | Bfs | BfsDist | Bfsinvp 
  | Induct

val file : string
val cin : in_channel

val max_proc : int
val type_only : bool
val maxrounds : int
val maxnodes : int

val only_forward : bool
val gen_inv : bool
val forward_inv : int
val enumerative : int
val lazyinv : bool
val refine : bool
val stateless : bool
val post_strategy : int
val delete : bool
val simpl_by_uc : bool
val bitsolver : bool

val cores : int

val mode : mode

val debug : bool
val dot : bool
val quiet : bool
val verbose : int

val debug_smt : bool
val dmcmt : bool
val profiling : bool
