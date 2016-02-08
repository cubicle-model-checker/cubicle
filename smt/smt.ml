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
  | AltErgo -> (module Alt_ergo : Smt_sig.S)
  | AltErgoFile -> (module Alt_ergo_file : Smt_sig.S)
  | AltErgoLib -> (module Alt_ergo_lib : Smt_sig.S)
  | Z3 -> (module Z3wrapper : Smt_sig.S)

module Selected_Smt : Smt_sig.S = (val (select_solver)) 

include Selected_Smt
