open Ast
open Types

let tbool = Hstring.make "mbool"

let pp_type fmt t =
  if Hstring.equal t tbool then Format.fprintf fmt "bool"
  else Format.fprintf fmt "%a" Hstring.print t

let pp_sep_pv fmt () = Format.fprintf fmt ";"

let pp_ltype fmt tl =
  Format.fprintf fmt "@[<h>%a"
    (Format.pp_print_list ~pp_sep:pp_sep_pv pp_type) tl;
  Format.fprintf fmt "@]"

let pp_sep_or fmt () = Format.fprintf fmt " || "

let pp_dnf fmt dnf =
  Format.fprintf fmt "@[<hov>%a"
    (Format.pp_print_list ~pp_sep:pp_sep_or SAtom.print) dnf;
  Format.fprintf fmt "@]"

let pp_sep_inst fmt () = Format.fprintf fmt ";@,"
let pp_sep_break fmt () = Format.fprintf fmt "@,"
    
let pp_glob_upd fmt = function
  | UTerm t -> Format.fprintf fmt "%a" Term.print t
  | UCase sw ->
      Format.fprintf fmt "@[<v 2>case@,%a@]"
        (Format.pp_print_list ~pp_sep:pp_sep_break (fun fmt (sa, t) ->
             Format.fprintf fmt "| %a : %a"
               SAtom.print sa Term.print t
           )
        ) sw

let pp_update fmt u =
  Format.fprintf fmt "%a[%a] := @[<v 2>case@,%a@]"
    Hstring.print u.up_arr Variable.print_vars u.up_arg
    (Format.pp_print_list ~pp_sep:pp_sep_break (fun fmt (sa, t) ->
         Format.fprintf fmt "| %a : %a"
           SAtom.print sa Term.print t
       )
    ) u.up_swts

let pp_nondet fmt nd = Format.fprintf fmt "%a := ." Hstring.print nd
    
let print_cub s file =
  Format.printf "@[<v>@[<v>";
  (* Global variables *)
  List.iter (fun (_, g, t) ->
      Format.printf "@[<h>var %a : %a@]@;" Hstring.print g pp_type t
    ) s.globals;
  Format.printf "@]@;";

  (* Constants *)
  Format.printf "@[<v>";
  List.iter (fun (_, c, t) ->
      Format.printf "@[<h>%a : %a@]@;" Hstring.print c pp_type t
    ) s.consts;
  Format.printf "@]@;";

  (* Arrays *)
  Format.printf "@[<v>";
  List.iter (fun (_, a, (lti, tv)) ->
      Format.printf "@[<h>array %a[%a] : %a@]@;"
        Hstring.print a pp_ltype lti pp_type tv
    ) s.arrays;
  Format.printf "@]@;";

  (* Type definitions *)
  Format.printf "@[<v>";
  List.iter (fun (_, (tn, cl)) ->
      if not (Hstring.equal tn tbool) then
        Format.printf "@[<h>type %a = %a@]@;"
          Hstring.print tn (Hstring.print_list " | ") cl
    ) s.type_defs;
  Format.printf "@]@;";

  (* Init formula *)
  Format.printf "@[<v>";
  let (_, vl, dnf) = s.init in
  Format.printf "@[<h>init(%a) @[<hov>{%a}@]@]@;"
    Variable.print_vars vl pp_dnf dnf;
  Format.printf "@]@;";

  (* Invs *)
  Format.printf "@[<v>";
  List.iter (fun (_, vl, sa) ->
      Format.printf "@[<h>invariant (%a) : {%a}@]@;"
        Variable.print_vars vl SAtom.print sa
    ) s.invs;
  Format.printf "@]@;";

  (* Unsafe *)
  Format.printf "@[<v>";
  List.iter (fun (_, vl, sa) ->
      Format.printf "@[<h>unsafe (%a) : {%a}@]@;"
        Variable.print_vars vl SAtom.print sa
    ) s.unsafe;
  Format.printf "@]@;";

  (* Transitions *)
  Format.printf "@[<v>";
  List.iter (fun ti ->
      Format.printf "@[<v>transition %a (%a)@,\
                     requires {@[<hov>%a@,%a@]}@,\
                     {@[<v 2>@,%a@,%a@,%a@]@,}\
                     @]@;"
        (* Name *)
        Hstring.print ti.tr_name
        (* Args *)
        (Hstring.print_list " ") ti.tr_args
        (* Reqs *)
        SAtom.print ti.tr_reqs
        (* Ureq *)
        (Format.pp_print_list ~pp_sep:pp_sep_break
           (fun fmt (v, dnf) ->
              Format.fprintf fmt "forall_other %a. %a"
                Hstring.print v pp_dnf dnf
           )
        ) ti.tr_ureq
        (* Assigns *)
        (Format.pp_print_list ~pp_sep:pp_sep_inst
           (fun fmt (v, gu) ->
              Format.fprintf fmt "%a := %a"
                Hstring.print v pp_glob_upd gu
           )
        ) ti.tr_assigns
        (* Upds *)
        (Format.pp_print_list ~pp_sep:pp_sep_inst pp_update) ti.tr_upds
        (* Nondets *)
        (Format.pp_print_list ~pp_sep:pp_sep_inst pp_nondet) ti.tr_nondets
        
    ) s.trans;
  
  Format.printf "@]@;";
  exit 0
