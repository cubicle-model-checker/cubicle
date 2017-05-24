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

open Ast

module HH = Hstring.H
  

type env = {
  constr_to_int : int HH.t;
  mcmt_vars : Hstring.t HH.t;
  local_vars : Hstring.t HH.t;
  mutable local_code : int;
}


let env = {
  constr_to_int = HH.create 31;
  mcmt_vars = HH.create 31;
  local_vars = HH.create 5;
  local_code = 120;
}

let () =
  HH.add env.mcmt_vars htrue (Hstring.make "true");
  HH.add env.mcmt_vars hfalse (Hstring.make "false")
  

let type_def fmt (t, l) = match l with
  | [] ->
      fprintf fmt ":smt (define-type %a)" Hstring.print t
  | _ ->
      let cpr = ref 0 in
      List.iter (fun c ->
        incr cpt;
        HH.add env.constr_to_int c !cpt) l;
      fprintf fmt ":smt (define-type %a (subrange 1 %d)" Hstring.print t !cpt;

let find_var first h =
  let chr_code = ref first in
  fun v ->
    try HH.find h
    with Not_found ->
      assert (!chr_code <= 255);
      let av = Hstring.make (String.make 1 (Char.chr !chr_code)) in
      incr chr_code;
      HH.add h v av;
      av

let find_var_name = find_var 97 env.mcmt_vars
let find_var_local = HH.find env.local_vars


let add_local_var v =
  try HH.find env.local_vars
    with Not_found ->
      assert (!chr_code <= 255);
      let av = Hstring.make (String.make 1 (Char.chr !chr_code)) in
      env.local_code <- env.local_code + 1;
      HH.add env.local_vars v av
        
let reset_local_vars =
  HH.clear env.local_vars;
  env.first_local_code <- 120;
  List.iter add_local_var
  
  
let hproc = Hstring.make proc
        
let print_mcmt_type fmt ty =
  if Hstring.equal ty hproc then
    fprintf fmt "int"
  else Hstring.print fmt ty
  
let global_def fmt (g, ty) =
  let mg = find_var_name g in
  fprintf fmt ":comment var %a : %a\n" Hstring.print g Hstring.print ty;
  fprintf fmt ":global %a %a" Hstring.print mg print_mcmt_type ty

let array_def fmt (a, (args, ty)) =
  assert (List.length args = 1);
  let ma = find_var_name a in
  fprintf fmt ":comment array %a : %a\n" Hstring.print a Hstring.print ty;
  fprintf fmt ":local %a %a" Hstring.print ma print_mcmt_type ty;

let const_def fmt (c, ty) =
  let mc = find_var_name g in
  fprintf fmt ":comment const %a : %a\n" Hstring.print c Hstring.print ty;
  fprintf fmt ":eevar %a %a" Hstring.print mc print_mcmt_type ty

let print_mcmt_var fmt n =
  Hstring.print fmt (find_var_name n)
    
let print_local_var fmt n =
  Hstring.print fmt (find_var_local n)

let const fmt = function
  | ConstInt n | ConstReal n -> fprintf fmt "%s" (Num.string_of_num n)
  | ConstName n -> print_mcmt_var fmt n

let int_consts fmt mc =
  fprintf fmt "(+ ";
  MConst.iter (fun c i ->
    fprintf fmt "(* %d %a)" i const c
  ) mc;
   fprintf fmt ")"

let rec term fmt = function
  | Const mc -> int_consts fmt mc
  | Elem (x, Var) -> print_local_var fmt x
  | Elem (e, _) -> print_mcmt_var fmt e
  | Access (a, [x]) -> fprintf fmt "%a[%a]" print_mcmt_var a print_local_var x
  | Access (_, _) -> assert false
  | Arith (t, mc) -> fprintf fmt "(+ %a %a)" term t int_consts mc


let atom fmt = function
  | True -> fprintf fmt "true"
  | False ->  fprintf fmt "false"
  | Comp (t1, Eq, t2) -> fprintf fmt "(= %a %a)" term t1 term t2
  | Comp (t1, Neq, t2) -> fprintf fmt "(not (= %a %a))" term t1 term t2
  | Comp (t1, Le, t2) -> fprintf fmt "(<= %a %a)" term t1 term t2
  | Comp (t1, Lt, t2) -> fprintf fmt "(< %a %a)" term t1 term t2
  | Ite _ -> assert false

let cube fmt =
  SAtom.iter (fun a -> fprintf fmt " %a " atom a)

let init fmt (vars, dnf) =
  reset_local_vars vars;
  match dnf with
    | [sa] ->
        fprintf fmt ":inital\n";
        List.iter (fun x ->
          fprintf fmt ":var %a\n" print_local_var x) vars;
        fprintf fmt ":cnj %a" cube sa
    | _ -> assert false


let unsafe (vars, dnf) =
  reset_local_vars vars;
  fprintf fmt ":unsafe\n";
  List.iter (fun x ->
    fprintf fmt ":var %a\n" print_local_var x) vars;
  List.iter (fun sa -> fprintf fmt ":u_cnj %a\n" cube sa) dnf


let update_dnf { up_arr = a; up_args = args; up_swts = swts} =
  let up_t = Access (a, args) in
  List.map (fun (sa, t) -> (sa, (up_t, t))) swts

let fact_updates upds =
  
    
let transition { tr_name = n;
                 tr_args = args;
                 tr_reqs = reqs;
                 tr_ureq = ureqs;
                 tr_assigns = assigns;
                 tr_upds = upds;
                 tr_nondets = nondets; } =
  reset_local_vars args;
  fprintf fmt ":comment transition %a\n" Hstring.print n;
  fprintf fmt ":transition\n";
  List.iter (fun x ->
    fprintf fmt ":var %a\n" print_local_var x) args;
  if ureqs <> [] then fprintf fmt ":var j\n";
  fprintf fmt ":guard %a\n" cube reqs;
  begin match ureqs with
    | [] -> ()
    | [dnf] -> List.iter (fun sa -> fprintf fmt ":uguard %a\n" cube sa) dnf
    | _ -> assert false
  end;    
  

      


















