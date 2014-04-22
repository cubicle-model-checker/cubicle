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

open Format
open Ast

(** Typing of parameterized systems *)


type error 

exception Error of error 

val report : Format.formatter -> error -> unit

val system : system -> t_system
(** Types an untyped system and performs subtyping analysis is the flag
    {! Options.subtyping} is [true]. *)
