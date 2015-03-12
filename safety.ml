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

(* TSO : Check if a trace is really Unsafe, TSO-wise *)
let validate_trace s n =

  (* Initialize buffers *)
  let bufs = MH.empty in

  (* Initialize initial state with (uninitialized) buffered variables *)
  let st = List.fold_left (fun st bv ->
    MH.add bv None st
  ) MH.empty s.t_buffered in

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
            begin match MH.find v st with
            | None -> MH.add v (Some t) st
            | Some ot ->
                if Term.compare t ot = 0 then st
                else failwith "Init is UnSAT"
            end with Not_found -> st
          end
      | _ -> st (* Warning : this could ignore some VarBs *)
    ) sa st
  ) st (snd s.t_init) in

  (* Buffer flush interleaving function *)
  let rec flush_interleave pred cont bufs st =
    if pred bufs st then cont bufs st else
    MH.iter (fun btid buf -> try
      let ((bvar, wt), buf) = FIFO.pop buf in
      let bufs = MH.add btid buf bufs in
      let st = MH.add bvar (Some wt) st in
      flush_interleave pred cont bufs st
      with FIFO.Empty -> ()
    ) bufs
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
    | (tid, Write (var, wt)) :: ops ->
        let buf = try MH.find tid bufs with Not_found -> FIFO.empty in
        let buf = FIFO.push (var, wt) buf in
        let bufs = MH.add tid buf bufs in
        follow_trace bufs st ops

    (* Read operation *)
    | (tid, Read (var, rt, eq)) :: ops ->
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
              let st = MH.add var (Some rt) st in
              follow_trace bufs st ops; false
          | Some mt ->
              eq <> (Term.compare rt mt <> 0)
          end with Not_found -> assert false (* We added all VarBs beforehand *)
        in
        let cont bufs st = follow_trace bufs st ops in
        flush_interleave valid cont bufs st
  in

  follow_trace bufs st n.ops

(* TSO : print memory operation trace *)
let print_tso_trace n =
  Format.fprintf std_formatter "Memory trace :\n";
  List.iter (fun (p, op) -> match op with
    | Read (var, t, eq) ->
        Format.fprintf std_formatter "%s:%s %s %a . "
        (Hstring.view p) (Hstring.view var)
        (if eq then "=" else "<>") Types.Term.print t
    | Write (var, t) ->
        Format.fprintf std_formatter "%s:%s <- %a . "
        (Hstring.view p) (Hstring.view var) Types.Term.print t
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
