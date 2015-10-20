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

(** The Alt-Ergo zero SMT library

    This SMT solver is derived from {{:http://alt-ergo.lri.fr} Alt-Ergo}. It
    uses an efficient SAT solver and supports the following quantifier free
    theories:
    - Equality and uninterpreted functions
    - Arithmetic (linear, non-linear, integer, reals)
    - Enumerated data-types

    This API makes heavy use of hash-consed strings. Please take a moment to
    look at {! Hstring}.
*)

include Smt_sig.S
