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

module FixpointList : sig
  val pure_smt_check : Node.t -> Node.t list -> int list option
  val check : Node.t -> Node.t list -> int list option
end

module FixpointTrie : sig
  val check : Node.t -> Node.t Cubetrie.t -> int list option
end
