(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

module type S = sig

    (** Interface for oracles

        Oracles provide a way to discard candidate invariants. The safety and
        correctness of Cubicle does not depend on the oracle, so any answer
        can be returned. However the efficiency of BRAB does. So the more
        precise the oracle, the better !

     *)

    val init : Ast.t_system -> unit
    (** Initialize the oracle on a given system *)


    val first_good_candidate : Node.t list -> Node.t option 
    (** Given a list of candidate invariants, returns the first one that seems
        to be indeed an invariant. *)

    val all_good_candidates : Node.t list -> Node.t list 
    (** Given a list of candidate invariants, returns the ones that seem
        to be indeed invariants. *)

end
