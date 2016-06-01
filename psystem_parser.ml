open Lexing
open Util
open Types
open Ptree

exception Found

let buffer_l = ref (-1)
let buffer_c = ref (-1)
let last_visited = ref None
  
let compare_motion l buffer   =
  let start_loc, stop_loc = l.loc in
  if !buffer_c > start_loc.pos_cnum && !buffer_c <= stop_loc.pos_cnum then
    let start_iter = buffer#get_iter (`OFFSET start_loc.pos_cnum) in
    let stop_iter = buffer#get_iter (`OFFSET stop_loc.pos_cnum) in
    ((match !last_visited with
      |None -> ()
      |Some (inf , start, stop ) ->
        if (inf.id <> l.id ) then
          buffer#remove_tag_by_name "gray_background" ~start:start ~stop:stop)
    ;
     (if l.active then
         buffer#apply_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter              else
         buffer#remove_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter);
     last_visited := Some (l, start_iter, stop_iter);
     raise Found)

let compare_button_press buffer  =
  match !last_visited with 
    |None -> ()
    |Some (inf,_ , _)-> 
      let start_loc, stop_loc = inf.loc in
      if !buffer_c >= start_loc.pos_cnum && !buffer_c <= stop_loc.pos_cnum then
        let start_iter = buffer#get_iter (`OFFSET start_loc.pos_cnum) in
        let stop_iter = buffer#get_iter (`OFFSET stop_loc.pos_cnum) in
        (if inf.active then 
            (buffer#remove_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter;   
             buffer#apply_tag_by_name "delete" ~start:start_iter ~stop:stop_iter)
         else 
            (buffer#remove_tag_by_name "delete" ~start:start_iter  ~stop:stop_iter););
        inf.active <- not (inf.active);
        last_visited := None

let cancel_last_visited buffer = 
  match !last_visited with
    |None -> ()
    |Some (id, start, stop) ->
      ( buffer#remove_tag_by_name "gray_background" ~start:start ~stop:stop;
        last_visited := None)

let parse_show_tag l buffer  = 
  if not l.active then
    let start_loc, stop_loc = l.loc in
    let start_iter = buffer#get_iter (`OFFSET start_loc.pos_cnum) in
    let stop_iter = buffer#get_iter (`OFFSET stop_loc.pos_cnum) in
    buffer#apply_tag_by_name "delete" ~start:start_iter ~stop:stop_iter
      
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
  |PNot (not_i, form ,i) -> f not_i buffer; parse_formula f buffer form; f i buffer
  |PAnd (l,i) 
  |POr (l,i) -> List.iter (parse_formula f buffer) l ; f i buffer
  |PImp (form1, form2, i) 
  |PEquiv (form1, form2, i) -> 
    parse_formula f buffer form1; parse_formula f buffer form2; f i buffer
  |PIte (form1, form2, form3, i) ->  
    parse_formula f buffer form1; parse_formula f buffer form2;
    parse_formula f buffer form3; f i buffer
  |PForall (vl, form, i) 
  |PExists (vl, form, i)
  |PForall_other (vl, form, i)
  |PExists_other (vl, form, i) -> parse_formula f buffer form; f i buffer

let rec parse_pswts f buffer p =  
  List.iter (fun x -> 
    parse_formula f buffer x.pup_form ;
    parse_term f buffer x.pup_t;
    f x.pup_i buffer) p

let rec parse_pupds f buffer p = function 
  |None -> let (x,_) =  p.pup_swts in  parse_pswts f buffer x ;f p.pup_loc buffer 
  |Some(_) -> f p.pup_loc buffer

let parse_nondets f buffer n = 
  f n.n_n.hstr_i buffer;
  f n.n_i buffer

let parse_assigns f buffer a = 
  f a.a_n.hstr_i buffer;
  match a.a_p with
    |PUTerm(_,i)
    |PUCase(_,i) -> f i buffer;
      f a.a_i buffer

let parse_ptrans f  buffer t =
  f t.ptr_name.hstr_i buffer;
  parse_formula f buffer t.ptr_reqs.r_f ;
  f t.ptr_reqs.r_i buffer;
  List.iter (fun x -> f x.hstr_i buffer) t.ptr_args;
  List.iter (fun n ->  f n.n_n.hstr_i buffer; f n.n_i buffer) t.ptr_s.ptr_nondets;
  List.iter (parse_assigns f buffer) t.ptr_s.ptr_assigns;
  List.iter (fun x ->
    let (_, i) = x.pup_swts in
    (* if x.pup_info <> None then *)
    (*   f i buffer ; f x.pup_arr.hstr_i buffer; *)
    (List.iter (fun x -> f x.hstr_i buffer) x.pup_arg);parse_pupds f buffer x x.pup_info)
    t.ptr_s.ptr_upds.t_pup_l;
  f t.ptr_s.ptr_upds.t_pup_i buffer; f t.ptr_s.ptr_i buffer;  f t.ptr_loc buffer

let parse_pform f  buffer p = 
  let (x, vl, form) =  p in 
  parse_formula f buffer form;
  List.iter (fun x -> f x.hstr_i buffer) vl ;
  f x buffer

let parse_type_defs f buffer t =
  let (inf,(name , l)) = t in
  List.iter (fun x -> f x.hstr_i buffer) l;
  f name.hstr_i buffer;
  f  inf buffer

let parse_glob_const f buffer x =
  let (i, h, t) = x in 
  f h.hstr_i buffer;
  f t.hstr_i buffer;
  f i buffer

let parse_array f  buffer x  =
  let (i, h, (l,t)) = x in 
  f h.hstr_i buffer;
  f t.hstr_i buffer;
  List.iter (fun x -> f x.hstr_i buffer) l;
  f i buffer

let parse f p buffer = 
  try
    List.iter (parse_glob_const f buffer) p.pglobals;
    List.iter (parse_glob_const f buffer) p.pconsts;
    List.iter (fun (x,_,_) -> f x buffer) p.pconsts;
    List.iter (parse_array f buffer) p.parrays;
    List.iter (parse_type_defs f buffer) p.ptype_defs;
    parse_pform f buffer p.pinit;
    List.iter (parse_pform f buffer) p.pinvs;
    List.iter (parse_pform f buffer) p.punsafe;
    List.iter (parse_ptrans f buffer) p.ptrans;
  with Found -> ()
    
let parse_tag p buffer = 
  parse (parse_show_tag) p buffer

let parse_psystem p buffer = 
  parse compare_motion p buffer
    
let parse_psystem_m p buffer = 
  compare_button_press buffer;
  parse_tag p buffer

    

