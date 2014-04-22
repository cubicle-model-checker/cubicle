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

open Ast

(** Certificate traces for external verifiers *)


(** The interface of certificate generators *)
module type S = sig

    (** this takes a system in input and the list of visited nodes, of which
        the disjunction constitutes an inductive invariant for the system.*)
    val certificate : t_system -> Node.t list -> unit
    (** [certificate s visited] must write on the disk a certificate of induction
        (initialization, preservation, and implication) and print the location
        of the generated certificate on stdout. *)
  end


(** A certificate generator for the SMT solver Alt-Ergo *)
module AltErgo : S


(** A certificate generator for the deductive platform Why3. These certificates
    can be verified by a {e herd} of automated provers *)
module Why3 : S

(** The certificate generator selected by the command line options. Contains a
    dummy generator if no [-trace] option was specified. *)
module Selected : S
