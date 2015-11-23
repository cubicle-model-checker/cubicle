(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2015                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

(** Oracle for BRAB that calls the explicit state model checker
    {{:http://formalverification.cs.utah.edu/Murphi/}Murphi}.

    We recommend the distribution
    {{:http://mclab.di.uniroma1.it/site/index.php/software/18-cmurphi}CMurphi}
    which works with most recent compilers.
*)

val print_system : int -> int -> Format.formatter -> Ast.t_system -> unit
(** [print_system p a fmt sys] prints the system [sys] in Murphi's syntax with
    [p] processes and infinite types abstracted with the subrange \[1;[a]\]. *)

(** {2 Oracle interface } *)

(** see {! Oracle.S} *)

include Oracle.S
