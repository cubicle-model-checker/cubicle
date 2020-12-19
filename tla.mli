(**************************************************************************)
(*                                                                        *)
(*                       Extension to Cubicle                             *)
(*                                                                        *)
(*                       Copyright (C) 2018                               *)
(*                                                                        *)
(*                        Philippe Queinnec                               *)
(*                          INP Toulouse                                  *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

(* Translate a Cubicle transition system into TLA+ *)
  
val print : out_channel -> Ast.system -> unit
    
