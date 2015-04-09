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
open Options
open Ast

exception Unsafe of Node.t

(*************************************************)
(* Safety check : n /\ init must be inconsistent *)
(*************************************************)

let cdnf_asafe ua =
  List.exists (
    List.for_all (fun a ->
      Cube.inconsistent_2arrays ua a))


(* fast check for inconsistence *)
let obviously_safe { t_init_instances = init_inst; } n =
  let nb_procs = Node.dim n in
  let _, cdnf_ai = Hashtbl.find init_inst nb_procs in
  cdnf_asafe (Node.array n) cdnf_ai



open Types
module MH = Map.Make (Hstring)
module MHP = Map.Make (
  struct
    let compare (a, al) (b, bl) =
      let rec cmp_lists r l1 l2 =
        if r <> 0 then r else
        match l1, l2 with
        | [], [] -> 0
        | [], _ -> -1
        | _, [] -> 1
        | e1 :: l1, e2 :: l2 -> cmp_lists (Hstring.compare e1 e2) l1 l2
      in cmp_lists (Hstring.compare a b) al bl
    type t = Hstring.t * Hstring.t list
  end)

(* TSO : Check if a trace is really Unsafe, TSO-wise *)
let validate_trace s n =

  (* Initialize buffers *)
  let bufs = MH.empty in

  (* Initialize initial state with (uninitialized) buffered variables *)
  let st = List.fold_left (fun st bv ->
    let st = MHP.add (bv, []) None st in
    List.fold_left (fun st idx ->
      let idx = Hstring.make ("#" ^ (string_of_int idx)) in
      MHP.add (bv, [idx]) None st
    ) st [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
  ) MHP.empty s.t_buffered in

  (* Set buffered variables initial values *)
  (* Works only with equalities to constants *)
  let st = List.fold_left (fun st sa ->
    Types.SAtom.fold (fun a st ->
      match a with
      | Atom.Comp (Elem (v, Glob), Eq, (Const _ as t))
      | Atom.Comp (Elem (v, Glob), Eq, (Elem (_, Constr) as t))
      | Atom.Comp ((Const _ as t), Eq, Elem (v, Glob))
      | Atom.Comp ((Elem (_, Constr) as t), Eq, Elem (v, Glob)) -> 
          begin try
            begin match MHP.find (v, []) st with
            | None -> MHP.add (v, []) (Some t) st
            | Some ot ->
                if Term.compare t ot = 0 then st
                else failwith "Init is UnSAT (v)"
            end with Not_found -> st
          end
      | Atom.Comp (Access (v, procs), Eq, (Const _ as t))
      | Atom.Comp (Access (v, procs), Eq, (Elem (_, Constr) as t))
      | Atom.Comp ((Const _ as t), Eq, Access (v, procs))
      | Atom.Comp ((Elem (_, Constr) as t), Eq, Access (v, procs)) ->
          if List.length procs <> 1 then
            failwith "Can only handle arrays of dimension 1 for now" else
          List.fold_left (fun st idx ->
            let idx = Hstring.make ("#" ^ (string_of_int idx)) in
            begin try
              begin match MHP.find (v, [idx]) st with
              | None -> MHP.add (v, [idx]) (Some t) st
              | Some ot ->
                  if Term.compare t ot = 0 then st
                  else failwith "Init is UnSAT (a)"
              end with Not_found -> st
            end
          ) st [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
      | _ -> st (* Warning : this could ignore some VarBs *)
    ) sa st
  ) st (snd s.t_init) in

  (* Buffer flush interleaving function *)
  let rec flush_interleave pred cont bufs st =
    if pred bufs st then cont bufs st else
    MH.iter (fun btid buf -> try
      let ((bvar, wt), buf) = FIFO.pop buf in
      let bufs = MH.add btid buf bufs in
      let st = MHP.add bvar (Some wt) st in
      flush_interleave pred cont bufs st
      with FIFO.Empty -> ()
    ) bufs
  in

  (* Check if t1 and t2 compare as prescribed by op *)
  let comp_terms t1 op t2 =
    let res = Term.compare t1 t2 in
    (res = 0 && (op = Ceq || op = Cle || op = Cge)) ||
    (res < 0 && (op = Cneq || op = Cle || op = Clt)) ||
    (res > 0 && (op = Cneq || op = Cge || op = Cgt))
  in

  (* Follow trace function *)
  let rec follow_trace bufs st = function

    (* End of trace : it is correct, so the program is not safe *)
    | [] ->  Printf.printf "Really UNSAFE\n"; raise (Unsafe n)

    (* Fence *)
    | (tid, Fence) :: ops ->
        let valid bufs st =
          try FIFO.is_empty (MH.find tid bufs)
          with Not_found -> true
        in
        let cont bufs st = follow_trace bufs st ops in
        flush_interleave valid cont bufs st

    (* Write operation *)
    | (tid, Write (var, procs, wt)) :: ops ->
        let buf = try MH.find tid bufs with Not_found -> FIFO.empty in
        let buf = FIFO.push ((var, procs), wt) buf in
        let bufs = MH.add tid buf bufs in
        follow_trace bufs st ops

    (* Read operation *)
    | (tid, Read (var, procs, rt, op (*eq*))) :: ops ->
        (* If the variable is in the buffer *)
        try
          let buf = MH.find tid bufs in
          let _, wt = FIFO.find (fun ((bvar, bprocs), _) ->
            var = bvar && procs = bprocs) buf in
          if comp_terms wt op rt (*eq <> (Term.compare rt wt <> 0)*) then
            follow_trace bufs st ops
          else
            flush_interleave (fun bufs st -> try
              let buf = MH.find tid bufs in
              FIFO.for_all (fun ((bvar, bprocs), _) ->
                var <> bvar && procs = bprocs) buf &&
              match MHP.find (var, procs) st with
              | None -> assert false (* MUST be defined now *)
              | Some mt -> (*eq <> (Term.compare rt mt <> 0)*)
                  comp_terms mt op rt
              with Not_found -> assert false (* We added all VarBs before *)
            ) (fun bufs st -> follow_trace bufs st ops) bufs st
        (* Otherwise read from memory, flushing buffers as needed *)
        with Not_found -> try match MHP.find (var, procs) st with
          | None ->
              let st = MHP.add (var, procs) (Some rt) st in (* Case undefined *)
              follow_trace bufs st ops
          | Some mt ->
              if comp_terms mt op rt (*eq <> (Term.compare rt mt <> 0)*) then
                follow_trace bufs st ops
              else
                flush_interleave (fun bufs st -> try
                  match MHP.find (var, procs) st with
                  | None -> false (* We expect the value to be in memory *)
                  | Some mt -> (*eq <> (Term.compare rt mt <> 0)*)
                      comp_terms mt op rt
                  with Not_found -> assert false (* We added all VarBs before *)
                ) (fun bufs st -> follow_trace bufs st ops) bufs st
        with Not_found -> assert false (* We added all VarBs before *)
  in

  follow_trace bufs st n.ops

(* TSO : print memory operation trace *)
let print_tso_trace n =
  let string_of_cmpop = function
    | Ceq -> "=" | Cneq -> "<>"
    | Cle -> "<=" | Clt -> "<"
    | Cge -> ">=" | Cgt -> ">"
  in
  let string_of_procs procs =
    let rec aux s = function
    | [] -> ""
    | [p] -> "[" ^ s ^ (Hstring.view p) ^ "]"
    | p :: procs -> aux (s ^ (Hstring.view p) ^ ", ") procs
    in
    aux "" procs
  in
  Format.fprintf std_formatter "Memory trace :\n";
  List.iter (fun (p, op) -> match op with
    | Read (var, procs, t, op) ->
        Format.fprintf std_formatter "%s:%s%s %s %a . "
        (Hstring.view p) (Hstring.view var)
        (string_of_procs procs) (string_of_cmpop op)
        Types.Term.print t
    | Write (var, procs, t) ->
        Format.fprintf std_formatter "%s:%s%s <- %a . "
        (Hstring.view p) (Hstring.view var)
        (string_of_procs procs) Types.Term.print t
    | Fence ->
        Format.fprintf std_formatter "%s:* . "
        (Hstring.view p)
  ) n.ops;
  Format.fprintf std_formatter "\n\n"


let check s n = (* TSO *)
  (*Debug.unsafe s;*)
  try
    if not (obviously_safe s n) then
      begin
	Prover.unsafe s n;
	if not quiet then eprintf "\nUnsafe trace: @[%a@]@."
	  Node.print_history n;
        (* raise (Unsafe n) *)

        (* Print and check TSO trace *)
        print_tso_trace n;
        validate_trace s n (* raise Unsafe (n) if trace is correct *)

      end
  with
    | Smt.Unsat _ -> ()



        (*
        let valid bufs st =
          (* If the value is in the thread's buffer, use it *)
          let in_buffer, value_ok = try
            let buf = MH.find tid bufs in
            let wt = snd (FIFO.find (fun (bvar, _) -> var = bvar) buf) in
              true, eq <> (Term.compare rt wt <> 0)
            with Not_found -> false, false
          in
          if in_buffer then begin
            if value_ok then follow_trace bufs st ops; false
          end else
          (* Otherwise read the value from memory, flushing buffers as needed *)
          try begin match MH.find var st with
          | None ->
              let st = MH.add var (Some rt) st in (* Case undefined *)
              follow_trace bufs st ops; false
          | Some mt ->
              eq <> (Term.compare rt mt <> 0)
          end with Not_found -> assert false (* We added all VarBs beforehand *)
        in
        let cont bufs st = follow_trace bufs st ops in
        flush_interleave valid cont bufs st *)
