(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*  Amit Goel                                                             *)
(*  Copyright (c) 2012, Intel Corporation.                                *)
(*                                                                        *)
(* This Trie-based Reachability extension to Cubicle ("Software") is      *)
(* furnished under Intel BSD License Agreement and may only be used       *)
(* or copied in accordance with the terms of that agreement. No           *)
(* license, express or implied, by estoppel or otherwise, to any          *)
(* intellectual property rights is granted by this document. The          *)
(* Software is subject to change without notice, and should not be        *)
(* construed as a commitment by Intel Corporation to market, license,     *)
(* sell or support any product or technology. Unless otherwise provided   *)
(* for in the license under which this Software is provided, the          *)
(* Software is provided AS IS, with no warranties of any kind, express    *)
(* or implied. Except as expressly permitted by the Software license,     *)
(* neither Intel Corporation nor its suppliers assumes any                *)
(* responsibility or liability for any errors or inaccuracies that may    *)
(* appear herein. Except as expressly permitted by the Software           *)
(* license, no part of the Software may be reproduced, stored in a        *)
(* retrieval system, transmitted in any form, or distributed by any       *)
(* means without the express written consent of Intel Corporation.        *)
(*                                                                        *)
(**************************************************************************)

(** Trie, mapping cubes to value of type 'a *)
type 'a t

(** The empty trie. *)
val empty : 'a t

(** Add a mapping cube->v to trie *)
val add : Ast.Atom.t list -> 'a -> 'a t -> 'a t

(** Is cube subsumed by some cube in the trie? *)
val mem : Ast.Atom.t list -> Ast.t_system t -> int list option

(** Apply f to all values mapped to in the trie. *)
val iter : ('a -> unit) -> 'a t -> unit

(** Delete all values which satisfy the predicate p *)
val delete : ('a -> bool) -> 'a t -> 'a t

(** Apply f to all values whose keys (cubes) are subsumed by the given cube. *)
val iter_subsumed : ('a -> unit) -> Ast.Atom.t list -> 'a t -> unit

(** List of all values mapped by the trie *)
val all_vals : 'a t -> 'a list

(** All values whose keys (cubes) are not inconsistent with the given cube. *)
val consistent : Ast.Atom.t list -> 'a t -> 'a list
