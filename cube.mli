(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2013                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

type t =
 private {
   vars : Variable.t list;
   litterals : Atom.Set.t;
   array : Atom.Array.t;
 }

val create : Variables.t list -> Atom.Set.t -> t
val normal_form : t -> t
val create_normal : Atom.Set.t -> t

val size : t -> int
val card: t -> int

val inconsistent : ?use_sets:bool -> t -> bool
val inconsistent_2 : ?use_sets:bool -> t -> t -> bool

val inconsistent_array : Atom.Array.t -> bool


val simplify : t -> t
val elim_ite_simplify : t -> t list

val resolve_two : t -> t -> t option

val print :  Format.formatter -> t -> unit





val new_cube_id : unit -> int

val has_deleted_ancestor : t_system -> bool
val already_closed : t_system -> transition -> Hstring.t list -> t_system option

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
val pure_smt_fixpoint : t_system -> t_system list -> int list option
val fixpoint : 
  invariants: t_system list -> visited: t_system list ->
  t_system -> int list option

val fixpoint_trie : t_system -> Atom.t list -> t_system Cubetrie.t ref ->
  t_system Cubetrie.t ref -> t_system list ref -> int list option

val fixpoint_trie2 : t_system Cubetrie.t -> t_system -> int list option

val add_and_resolve : t_system -> t_system Cubetrie.t -> t_system Cubetrie.t

