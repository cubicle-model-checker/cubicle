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
  if !buffer_c >= start_loc.pos_cnum && !buffer_c < stop_loc.pos_cnum then
    let start_iter = buffer#get_iter (`OFFSET start_loc.pos_cnum) in
    let stop_iter = buffer#get_iter (`OFFSET stop_loc.pos_cnum) in
    ((match !last_visited with
    |None -> ()
    |Some (id, start, stop) ->
      if (id <> l.id ) then
        buffer#remove_tag_by_name "gray_background" ~start:start ~stop:stop)
    ;
     (if l.active then
         buffer#apply_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter          
      else
         buffer#remove_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter;);
     last_visited := Some (l.id, start_iter, stop_iter);
     raise Found)
      
let rec parse_term f buffer = function 
  |TVar (_, i) 
  |TTerm (_, i) -> f i buffer

let parse_atom f buffer = function
  |AVar (_, i) 
  |AAtom (_, i) -> f i buffer 
  |AEq (t1, t2, i) 
  |ANeq(t1, t2, i)
  |ALe(t1, t2, i)
  |ALt(t1, t2, i) -> parse_term f buffer t1; parse_term f buffer t2; f i buffer
                                                         
let rec parse_formula f buffer = function
  |PAtom (a) -> parse_atom f buffer a 
  |PNot (form ,i) -> parse_formula f buffer form; f i buffer
  |PAnd (l,i) 
  |POr (l,i) -> List.iter (fun x -> parse_formula f buffer x) l ;    f i buffer
  |PImp (form1, form2, i) 
  | PEquiv (form1, form2, i) -> 
    parse_formula f buffer form1; parse_formula f buffer form2; f i buffer
  |PIte (form1, form2, form3, i) ->  
    parse_formula f buffer form1; parse_formula f buffer form2; parse_formula f buffer form3; f i buffer
  |PForall (vl, form, i)
  |PExists (vl, form, i)
  |PForall_other (vl, form, i)
  |PExists_other (vl, form, i) -> parse_formula f buffer form; f i buffer

let rec parse_pswts f buffer p = 
   let (p_swts) = p in 
   List.iter (fun (form, t, i) ->
     parse_formula f buffer form; parse_term f buffer t; f i buffer) p_swts

let rec parse_pupds f buffer p = 
  parse_pswts f buffer p.pup_swts;
  f p.pup_loc buffer

let parse_ptrans f t buffer = 
  parse_formula f buffer t.ptr_reqs.r_f ;
  f t.ptr_reqs.r_i buffer;
  (* List.iter (fun x -> f x.i buffer) t.ptr_args; *)
  List.iter (fun x -> f x.n_i buffer) t.ptr_s.ptr_nondets;
  List.iter (fun x -> f x.a_i buffer) t.ptr_s.ptr_assigns;
  List.iter (parse_pupds f buffer) t.ptr_s.ptr_upds.p;
  f t.ptr_s.ptr_upds.i buffer;
  f t.ptr_s.i buffer;
  f t.ptr_loc buffer

let parse_pform f p buffer = 
  let (x,_,form) =  p in 
  parse_formula f buffer form;
  f x buffer
    
let parse_psystem p buffer = 
  try
    List.iter (fun (x,_,_) -> compare_location x buffer) p.pglobals;
    List.iter (fun (x,_,_) -> compare_location x buffer) p.pconsts;
    List.iter (fun (x,_,_) -> compare_location x buffer) p.parrays;
    List.iter (fun (x,_) -> compare_location x buffer) p.ptype_defs;
    parse_pform (compare_location) p.pinit buffer;
    List.iter (fun x -> parse_pform (compare_location) x buffer) p.pinvs;
    List.iter (fun x -> parse_pform (compare_location) x buffer) p.punsafe;
    List.iter (fun x -> parse_ptrans(compare_location) x buffer) p.ptrans;
  with Found -> ()
 
  
let compare_location_m l buffer=
  let start_loc, stop_loc = l.loc in
  if !buffer_c >= start_loc.pos_cnum && !buffer_c < stop_loc.pos_cnum then
    let start_iter = buffer#get_iter (`OFFSET start_loc.pos_cnum) in
    let stop_iter = buffer#get_iter (`OFFSET stop_loc.pos_cnum) in
    (if l.active then 
        (buffer#remove_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter;   
         buffer#apply_tag_by_name "delete" ~start:start_iter ~stop:stop_iter)
     else 
        (buffer#remove_tag_by_name "delete" ~start:start_iter  ~stop:stop_iter));
    l.active <- not (l.active);
    last_visited := None;
    raise Found

let parse_psystem_m p buffer =
  let f = parse_pform (compare_location_m) in 
  try
      List.iter (fun (x,_,_) -> compare_location_m x buffer) p.pglobals;
      List.iter (fun (x,_,_) -> compare_location_m x buffer) p.pconsts;
      List.iter (fun (x,_,_) -> compare_location_m x buffer) p.parrays;
      List.iter (fun (x,_) -> compare_location_m x buffer) p.ptype_defs;
      f p.pinit buffer;
      List.iter (fun x -> parse_pform (compare_location_m ) x buffer) p.pinvs;
      List.iter (fun x -> parse_pform (compare_location_m ) x buffer) p.punsafe;
      List.iter (fun x -> parse_ptrans (compare_location_m) x buffer) p.ptrans;
  with Found -> ()
