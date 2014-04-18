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

open Options
open Format

type t = Hstring.t

type subst = (t * t) list

module Set = Hstring.HSet

let gen_vars s n = 
  let l = ref [] in
  for i = 1 to max_proc do
    l := Hstring.make (s^(string_of_int i)) :: !l
  done;
  List.rev !l


let alphas = gen_vars "$" max_proc

let procs = gen_vars "#" max_proc

let freshs = gen_vars "?" max_proc


let proc_vars_int = 
  let l = ref [] in
  for i = 1 to max_proc do
    l := i :: !l
  done;
  List.rev !l


let number v =
  let s = Hstring.view v in
  if s.[0] = '#' then 
    int_of_string (String.sub s 1 (String.length s - 1))
  else 1


let build_subst args a_args =
  let rec a_subst acc args a_args =
    match args, a_args with
      | [], _ -> acc
      | x::args, ax::a_args ->
	a_subst ((x, ax)::acc) args a_args
      | _ -> assert false
  in
  a_subst [] args a_args


let subst sigma v = Hstring.list_assoc v sigma


let rec all_permutations l1 l2 = 
  (*assert (List.length l1 <= List.length l2);*)
  match l1 with
    | [] -> [[]]
    | x::l -> cross l [] x l2
and cross l pr x st =
  match st with
    | [] -> []
    | y::p -> 
	let acc = all_permutations l (pr@p) in
	let acc = 
	  if acc = [] then [[x,y]]
	  else List.map (fun ds -> (x, y)::ds) acc in
	acc@(cross l (y::pr) x p)

let rec all_parts l = match l with
  | [] -> []
  | x::r -> let pr = all_parts r in
	    [x]::pr@(List.map (fun p -> x::p) pr)

let all_parts_elem l = List.map (fun x -> [x]) l

let rec all_partial_permutations l1 l2 =
  List.flatten (
    List.fold_left (fun acc l -> (all_permutations l l2)::acc) [] (all_parts l1)
  )

let rec all_arrangements n l =
  assert (n > 0);
  match n with
    | 1 -> List.map (fun x -> [x]) l
    | _ -> 
        List.fold_left (fun acc l' ->
          List.fold_left (fun acc x -> (x :: l') :: acc) acc l
        ) [] (all_arrangements (n - 1) l)

let arity s = List.length (fst (Smt.Symbol.type_of s))

let rec all_arrangements_arity s l = all_arrangements (arity s) l


let rec all_instantiations l1 l2 =
  match l1 with
    | [] -> []
    | [x1] -> List.map (fun x2 -> [x1, x2]) l2
    | x1 :: r1 -> 
        List.fold_left (fun acc l' ->
          List.fold_left (fun acc x2 -> ((x1, x2) :: l') :: acc) acc l2
        ) [] (all_instantiations r1 l2)


let rec mix x = function
  | [] -> [[x]]
  | y::r as l -> 
     (x :: l) :: (List.map (fun l' -> y :: l') (mix x r))

let rec interleave l1 l2 = 
  let rec aux acc = function
    | [], [] -> acc
    | l, [] | [], l -> List.map (List.rev_append l) acc
    | (x :: r1 as l1), (y :: r2 as l2) ->
       let acc1 = List.map (fun n -> x :: n) acc in
       let acc1 = aux acc1 (r1, l2) in
       let acc2 = List.map (fun n -> y :: n) acc in
       let acc2 = aux acc2 (l1, r2) in
       List.rev_append acc1 acc2
  in
  aux [[]] (List.rev l1, List.rev l2)

let rec perms = function
  | [] -> [[]]
  | x :: r -> List.flatten (List.map (mix x) (perms r))


(* renamed in extra_procs *)
(* let extra_args args tr_args = *)
(*   let rec aux acc cpt = function *)
(*     | [] -> List.rev acc *)
(*     | _::r -> aux ((List.nth procs (cpt - 1)) :: acc) (cpt+1) r *)
(*   in *)
(*   aux [] (List.length args + 1) tr_args *)

let append_extra_procs_to acc args tr_args =
  let rec aux acc args tr_args procs =
    match args, tr_args, procs with
    | [], [], _ -> List.rev acc
    | [], x :: rtr, p :: rpr -> aux (p::acc) [] rtr rpr
    | a :: ra, _, p :: rpr -> aux acc ra tr_args rpr
    | _, _, [] -> failwith "Not enough procs"
  in
  aux (List.rev acc) args tr_args procs

let append_extra_procs args tr_args = append_extra_procs_to args args tr_args

let extra_procs args tr_args = append_extra_procs_to [] args tr_args

let rec first_n n l =
  assert (n >= 0);
  let rec aux acc = function
    | 0, _ | _, [] -> List.rev acc
    | n, x :: r -> aux (x :: acc) (n-1, r)
  in aux [] (n, l)

let missing args tr_args extra =
  let nb = List.length tr_args - List.length args in
  if nb <= 0 then []
  else first_n nb extra
    
let insert_missing l tr_args =
  let ex = extra_procs l tr_args in
  let ms = missing l tr_args ex in 
  List.flatten (List.map (fun x -> mix x l) ms)


let rec all_parts_max n l =
  List.filter (fun p -> List.length p <= n) (all_parts l)
  
let permutations_missing tr_args l =
  let parts = [] :: List.flatten 
		      (List.map perms (all_parts_max (List.length tr_args) l))
  in
  let ex = extra_procs l tr_args in
  let l' = List.fold_left 
    (fun acc l ->
     let ms = missing l tr_args ex in
     List.rev_append (interleave l ms) acc)
    [] parts in
  List.map (List.combine tr_args) l'
  (* List.map (insert_missing tr_args) parts *)


let extra_vars vs1 vs2 =
  let rec aux dif vs1 vs2 = match vs1, vs2 with
    | [], [] -> dif
    | _::_, [] -> vs1
    | [], _::_ -> dif
    | a::ra, b::rb -> aux dif ra rb
  in
  aux [] vs1 vs2



let print fmt v = Hstring.print fmt v

let rec print_vars fmt = function
  | [] -> ()
  | [a] ->
     let s = Hstring.view a in
     let s = if dmcmt then (String.sub s 1 (String.length s - 1)) else s in
     if dmcmt then fprintf fmt "_%s" s
     else fprintf fmt "%s" s
  | a::r -> 
     let s = Hstring.view a in
     let s = if dmcmt then (String.sub s 1 (String.length s - 1)) else s in
     if dmcmt then  fprintf fmt "_%s%a" s print_vars r
     else  fprintf fmt "%s, %a" s print_vars r

let rec print_subst fmt = function
  | [] -> ()
  | [x,y] ->
     fprintf fmt "%a -> %a" print x print y
  | (x,y)::r -> 
     fprintf fmt "%a -> %a, %a" print x print y print_subst r
