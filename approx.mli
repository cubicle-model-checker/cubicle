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


open Options
open Format
open Ast


val remove_bad_candidates : t_system -> Node.t -> Node.t list -> Node.t list

module type S = sig
    val good : Node.t -> Node.t option
end

module Make ( O : Oracle.S ) : S

module SelectedOracle : Oracle.S
module Selected : S
