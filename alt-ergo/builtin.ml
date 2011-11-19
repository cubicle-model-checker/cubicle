(**************************************************************************)
(*                                                                        *)
(*     The Alt-ergo theorem prover                                        *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

let symbols = Hashtbl.create 97

let ale = Hstring.make "<=" 
let alt = Hstring.make "<"
let agt = Hstring.make ">"

let is_le n = Hstring.compare n ale = 0
let is_lt n = Hstring.compare n alt = 0
let is_gt n = Hstring.compare n agt = 0



let () = 
  List.iter 
    (fun (x,y) -> Hashtbl.add symbols x y) 
       [ "<=", ale; 
         "<", alt ]


let is_builtin = Hashtbl.find symbols
