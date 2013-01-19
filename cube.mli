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

open Format
open Options
open Ast
open Atom

val new_cube_id : unit -> int

val has_deleted_ancestor : t_system -> bool
val already_closed : t_system -> transition -> Hstring.t list -> t_system option

val all_permutations : 'a list -> 'b list -> ('a * 'b) list list

val apply_subst : SAtom.t -> (Hstring.t * Hstring.t) list -> SAtom.t

val add_constants : int MConst.t -> int MConst.t -> int MConst.t

val proper_cube : SAtom.t -> SAtom.t * (Hstring.t list * Hstring.t)
val args_of_atoms : SAtom.t -> Hstring.t list

val simplification_atoms : SAtom.t -> SAtom.t -> SAtom.t
val simplify_atoms : SAtom.t -> SAtom.t list

val inconsistent_2cubes : SAtom.t -> SAtom.t -> bool
val inconsistent_list : Atom.t list -> bool
val inconsistent : SAtom.t -> bool

val all_var_terms : Hstring.t list -> t_system -> STerm.t

val size_system : t_system -> int
val card_system : t_system -> int

val check_safety : t_system -> unit

val easy_fixpoint : t_system -> t_system list -> int list option
val hard_fixpoint : t_system -> t_system list -> int list option
val fixpoint : 
  invariants: t_system list -> visited: t_system list ->
  t_system -> int list option

val fixpoint_trie : t_system -> Atom.t list -> t_system Cubetrie.t ref ->
  t_system Cubetrie.t ref -> t_system list ref -> int list option

val fixpoint_trie2 : t_system Cubetrie.t -> t_system -> int list option

val add_and_resolve : t_system -> t_system Cubetrie.t -> t_system Cubetrie.t
val simple_extract_candidates :
  ArrayAtom.t -> ArrayAtom.t list list -> SAtom.t list
