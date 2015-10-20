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

let select_solver =
  match smt_solver with
  | "alt-ergo" -> (module Alt_ergo : Smt_sig.S)
  | "z3" -> (module Z3wrapper : Smt_sig.S)
  | _ -> failwith ("The solver "^ smt_solver ^" is not available.")

module Selected_Smt : Smt_sig.S = (val (select_solver)) 

include Selected_Smt
