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


open Options
open Format
open Ast


(** {b Approximations and candidates generation } *)

val remove_bad_candidates : t_system -> Node.t -> Node.t list -> Node.t list
(** Register bad candidates and try to infer as much inforamtion as possible
    from the error trace before the restart.*)

(** {3 Interface } *)


module type S = sig
    val good : Node.t -> Node.t option
    (** Returns a good approximation in the form of a candidate invariant if
        the oracle was able to find one. *)
end

module Make ( O : Oracle.S ) : S
(** Functor for creating an approximation procedure from an oracle *)

module SelectedOracle : Oracle.S
(** The oracle selected by the command line options *)

module Selected : S
(** The approximation module constructed with the oracle selected by the
    command line options *)

