(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Universite Paris-Sud 11              *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

type mode = Dfs | DfsL | DfsH | DfsHL | Bfs | BfsDist | Bfsinvp

val file : string
val cin : in_channel

val type_only : bool ref
val maxrounds : int
val maxnodes : int

val gen_inv : bool
val alwayspost : bool
val delete : bool
val simpl_by_uc : bool

val cores : int

val mode : mode

val debug : bool
val verbose : int ref

val debug_altergo : bool
val profiling : bool
