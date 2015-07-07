open Ast
open Types

(** the type of instantiated transitions *)
type inst_trans =
    {
      i_reqs : SAtom.t;
      i_udnfs : SAtom.t list list;
      i_actions : SAtom.t;
      i_touched_terms : Term.Set.t;
      i_args : Variable.t list;
    }

(** instantiate transitions with a list of possible parameters *)
val instantiate_transitions : Variable.t list -> Variable.t list ->
  transition list -> inst_trans list

val prime_match_satom : SAtom.t -> Term.Set.t -> SAtom.t
