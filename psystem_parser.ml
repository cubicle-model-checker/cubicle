open Lexing
open Util
open Types
open Ptree

exception Found

let buffer_l = ref (-1)
let buffer_c = ref (-1)
let last_visited = ref None
  
let compare_location l buffer  =
  let start_loc, stop_loc = l.loc in
  let b_l, b_c = !buffer_l, !buffer_c in
  let l_start, c_start = start_loc.pos_lnum, start_loc.pos_cnum in
  let l_stop, c_stop = stop_loc.pos_lnum, stop_loc.pos_cnum in
    if l_start == l_stop && l_start == b_l && b_c >= c_start && b_c < c_stop
       || l_start == b_l && l_stop <> l_start && b_c >= c_start 
       || l_stop == b_l && l_stop <> l_start && b_c < c_stop 
       || b_l > l_start && b_l < l_stop  then
      let start_iter = buffer#get_iter (`OFFSET c_start) in
      let stop_iter = buffer#get_iter (`OFFSET c_stop) in
      ((match !last_visited with
        |None -> ()
        |Some (id, start, stop) ->
          Printf.printf "%d %d\n" id l.id;
          if (id <> l.id ) then
            buffer#remove_tag_by_name "gray_background" ~start:start ~stop:stop)
      ;
       (if l.active then
           buffer#apply_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter              else
           buffer#remove_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter;);
       last_visited := Some (l.id, start_iter, stop_iter);
       raise Found)

let parse_atom  f buffer = function
  |AVar (_, i) 
  |AAtom (_, i) 
  |AEq (_, _, i)
  |ANeq(_,_,i)
  |ALe(_,_,i)
  |ALt(_,_,i) -> f i buffer
                                                         
let rec parse_formula f buffer = function
  |PAtom a -> parse_atom buffer a 
  |PNot (form ,i) -> parse_formula f buffer form; f i buffer
  |PAnd (l,i) | POr (l,i) -> List.iter (fun x -> parse_formula f buffer x) l ;
    f i buffer
  |_ -> ()


let parse_ptrans f t buffer = 
  parse_formula buffer t.ptr_reqs.r_f ;
  f t.ptr_reqs.r_i buffer;
  List.iter (fun x -> f x.n_i buffer) t.ptr_nondets;
  List.iter (fun x -> f x.a_i buffer) t.ptr_assigns;
  List.iter (fun x -> f x.pup_loc buffer) t.ptr_upds;
  f t.ptr_loc buffer 

let parse_pform f buffer = 
  let (x,_,form) =  p in 
  parse_formula buffer form;
  f x buffer
    
let parse_psystem p buffer = 
  try
    List.iter (fun (x,_,_) -> compare_location x buffer) p.pglobals;
    List.iter (fun (x,_,_) -> compare_location x buffer) p.pconsts;
      List.iter (fun (x,_,_) -> compare_location x buffer) p.parrays;
      List.iter (fun (x,_) -> compare_location x buffer) p.ptype_defs;
      parse_pform p.pinit buffer;
      List.iter (fun x -> parse_pform (compare_location) x buffer) p.pinvs;
      List.iter (fun x -> parse_pform (compare_location) x buffer) p.punsafe;
      List.iter (fun x -> parse_ptrans(compare_location) x buffer) p.ptrans;
  with Found -> ()
 
  
let compare_location_m l buffer=
  let start_loc, stop_loc = l.loc in
  let b_l, b_c = !buffer_l, !buffer_c in
  let l_start, c_start = start_loc.pos_lnum, start_loc.pos_cnum in
  let l_stop, c_stop = stop_loc.pos_lnum, stop_loc.pos_cnum in
 if l_start == l_stop && l_start == b_l && b_c >= c_start && b_c < c_stop
       || l_start == b_l && l_stop <> l_start && b_c >= c_start 
       || l_stop == b_l && l_stop <> l_start && b_c < c_stop 
       || b_l > l_start && b_l < l_stop  then
    let start_iter = buffer#get_iter (`OFFSET c_start) in
    let stop_iter = buffer#get_iter (`OFFSET c_stop) in
    (if l.active then 
        (buffer#remove_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter;         buffer#apply_tag_by_name "delete" ~start:start_iter ~stop:stop_iter)
     else 
        (buffer#remove_tag_by_name "delete" ~start:start_iter  ~stop:stop_iter));
    l.active <- not (l.active);
    last_visited := None;
    raise Found

let parse_atom_m buffer = function
  |AVar (_, i) 
  |AAtom (_, i) 
  |AEq (_, _, i)
  |ANeq(_,_,i)
  |ALe(_,_,i)
  |ALt(_,_,i) -> compare_location_m i buffer
                                                         
let rec parse_formula_m buffer = function
  |PAtom a -> parse_atom_m buffer a 
  |PNot (f,i) -> parse_formula_m buffer f; compare_location_m i buffer
  |PAnd (l,i) | POr (l,i) -> List.iter (fun x -> parse_formula_m buffer x) l ;
    compare_location_m i buffer
  |_ -> ()

let parse_ptrans_m t buffer = 
  parse_formula_m buffer t.ptr_reqs.r_f ;
  compare_location_m t.ptr_reqs.r_i buffer;
  List.iter (fun x -> compare_location_m x.n_i buffer) t.ptr_nondets;
  List.iter (fun x -> compare_location_m x.a_i buffer) t.ptr_assigns;
  List.iter (fun x -> compare_location_m x.pup_loc buffer) t.ptr_upds;
  compare_location_m t.ptr_loc buffer 


let parse_pform_m p buffer = 
  let (x,_,f) =  p in 
  parse_formula_m buffer f;
  compare_location_m x buffer


let parse_psystem_m p buffer =
  try
      List.iter (fun (x,_,_) -> compare_location_m x buffer) p.pglobals;
      List.iter (fun (x,_,_) -> compare_location_m x buffer) p.pconsts;
      List.iter (fun (x,_,_) -> compare_location_m x buffer) p.parrays;
      List.iter (fun (x,_) -> compare_location_m x buffer) p.ptype_defs;
      parse_pform_m p.pinit buffer;
      List.iter (fun x -> parse_pform_m x buffer) p.pinvs;
      List.iter (fun x -> parse_pform_m x buffer) p.punsafe;
      List.iter (fun x -> parse_ptrans_m x buffer) p.ptrans;
  with Found -> ()
