open Lexing
open Util
open Types
open Ptree


exception Found

exception ParseRev

type tag = Comment | Hover | UndoComment | UndoHover

let tag_list = ref []
let buffer_l = ref (-1)
let buffer_c = ref (-1)
let last_visited = ref None
let test = ref None 
let inact_l = ref []

let compare_motion l   =
  let start_loc, stop_loc = l.loc in
  if !buffer_c >= start_loc.pos_cnum && !buffer_c < stop_loc.pos_cnum  then
    ((match !last_visited with
      |None -> ()
      |Some (inf, start, stop) ->
        if (inf.id <> l.id ) then
          tag_list := (UndoHover, start, stop)::!tag_list);
     (if l.active then 
         tag_list := (Hover, start_loc.pos_cnum, stop_loc.pos_cnum)::!tag_list
      else  
         tag_list := (UndoHover, start_loc.pos_cnum, stop_loc.pos_cnum)::!tag_list);
     last_visited := Some(l, start_loc.pos_cnum, stop_loc.pos_cnum);
     raise Found)

let compare_button_press l  =
  let start_loc, stop_loc = l.loc in
  if !buffer_c >= start_loc.pos_cnum && !buffer_c < stop_loc.pos_cnum  then
    if not l.active then  
      (tag_list := (UndoComment, start_loc.pos_cnum, stop_loc.pos_cnum)::!tag_list;
       l.active <- not (l.active);
       last_visited := None;
       raise Found)
        
let rec parse_term_info_rev f  = function
  |None -> ()
  |Some x ->
    List.iter (fun x -> f x.hstr_i) x.arr_arg;
    f x.arr_n.hstr_i 
      
let rec parse_term_rev f  = function 
  |TVar (_, i) -> f i 
  |TTerm ((_, i), arr_info) -> f i ; parse_term_info_rev f  arr_info

let parse_atom_rev f  = function
  |AVar (_, i) 
  |AAtom (_, i) -> f i 
  |AEq (t1, t2, i) 
  |ANeq(t1, t2, i)
  |ALe(t1, t2, i)
  |ALt(t1, t2, i) -> f i ; parse_term_rev f  t1; parse_term_rev f  t2 
    
let rec parse_formula_rev f = function
  |PAtom (a) -> parse_atom_rev f  a 
  |PNot (not_i, form , i) -> f i ; parse_formula_rev f  form; f not_i 
  |PAnd (l, i) 
  |POr (l, i) -> f i ; List.iter (parse_formula_rev f ) l 
  |PImp (form1, form2, i) 
  |PEquiv (form1, form2, i) -> 
    f i ; parse_formula_rev f  form1; parse_formula_rev f  form2
  |PIte (form1, form2, form3, i) ->  
    f i ; parse_formula_rev f  form1; parse_formula_rev f  form2;
    parse_formula_rev f  form3
  |PForall (vl, form, i) 
  |PExists (vl, form, i)
  |PForall_other (vl, form, i)
  |PExists_other (vl, form, i) ->
    parse_formula_rev f  form; f i ;
    List.iter (fun x -> f x.hstr_i ) vl
      
let rec parse_pswts_rev f  p =  
  List.iter (fun x -> 
    f x.pup_i ;
    parse_term_rev f  x.pup_t;
    parse_formula_rev f  x.pup_form 
  ) p

let rec parse_pupds_rev f  p = function 
  |None -> let (x, _) =  p.pup_swts in f p.pup_loc ; parse_pswts_rev f  x 
  |Some(_) -> f p.pup_loc 

let parse_nondets_rev f  n = 
  f n.n_i ;
  f n.n_n.hstr_i 
    
let parse_assigns_rev f  a = 
  match a.a_p with
    |PUTerm(_, i)
    |PUCase(_, i) ->   f a.a_i ; f i ;     
      f a.a_n.hstr_i 

let parse_ptrans_rev f   t =
  f t.ptr_loc ;
  f t.ptr_s.ptr_i ;
  f t.ptr_s.ptr_upds.t_pup_i ;
  List.iter (fun x ->
    let (_, i) = x.pup_swts in
    let (p_arg, parg_i) = x.pup_arg in
    if x.pup_info <> None then
      f x.pup_arr.hstr_i ; f i ;
    parse_pupds_rev f  x x.pup_info;
    f parg_i ;
    (List.iter (fun x -> f x.hstr_i ) p_arg))  t.ptr_s.ptr_upds.t_pup_l;

  List.iter (parse_assigns_rev f ) t.ptr_s.ptr_assigns;
  List.iter (fun n ->  f n.n_n.hstr_i ; f n.n_i ) t.ptr_s.ptr_nondets;
  List.iter (fun x -> f x.hstr_i ) t.ptr_args;
  parse_formula_rev f  t.ptr_reqs.r_f ;
  f t.ptr_name.hstr_i 

    
let parse_pform_rev f   p = 
  let (x, vl, form) =  p in 
  f x ;
  List.iter (fun x -> f x.hstr_i ) vl ;
  parse_formula_rev f  form
    
let parse_type_defs_rev f  t =
  let (inf, (name, l)) = t in
  f  inf ;
  f name.hstr_i ;
  List.iter (fun x -> f x.hstr_i ) l
    
let parse_glob_const_rev f  x =
  let (i, h, t) = x in 
  f i ;
  f t.hstr_i ;
  f h.hstr_i 
    
let parse_array_rev f   x =
  let (i, h, (l, t)) = x in 
  f i ;
  f t.hstr_i ;
  List.iter (fun x -> f x.hstr_i ) l;
  f h.hstr_i 


let build_inact  l   =
  let start_loc, stop_loc = l.loc in
  if not l.active then inact_l := (start_loc.pos_cnum, stop_loc.pos_cnum)::(!inact_l)
    
let parse_rev f p  = 
  try 
    List.iter (parse_glob_const_rev f  ) p.pglobals;
    List.iter (parse_glob_const_rev f  ) p.pconsts;
    List.iter (parse_array_rev f  ) p.parrays;
    List.iter (parse_type_defs_rev f  ) p.ptype_defs;
    parse_pform_rev f  p.pinit;
    List.iter (parse_pform_rev f  ) p.pinvs;
    List.iter (parse_pform_rev f  ) p.punsafe;
    List.iter (parse_ptrans_rev f  ) p.ptrans;
  with Found -> ()
    
    
let cancel_last_visited () =
  match !last_visited with
    |None -> []
    |Some (id, start, stop) ->
      last_visited := None;
      [( UndoHover, start,stop)]

let parse_show_tag l   = 
  if not l.active then
    let start_loc, stop_loc = l.loc in

    tag_list:=(Comment, start_loc.pos_cnum, stop_loc.pos_cnum)::(!tag_list)
      
let rec parse_term_info f  = function
  |None -> ()
  |Some x ->
    f x.arr_n.hstr_i ;
    List.iter (fun x -> f x.hstr_i ) x.arr_arg

let rec parse_term f  = function 
  |TVar (_, i) -> f i 
  |TTerm ((_, i),arr_info) -> parse_term_info f  arr_info; f i 

let parse_atom f  = function
  |AVar (_, i) 
  |AAtom (_, i) -> f i 
  |AEq (t1, t2, i) 
  |ANeq(t1, t2, i)
  |ALe(t1, t2, i)
  |ALt(t1, t2, i) -> parse_term f  t1; parse_term f  t2; f i   
    
let rec parse_formula f  = function
  |PAtom (a) -> parse_atom f  a 
  |PNot (not_i, form , i) -> f not_i ; parse_formula f  form; f i 
  |PAnd (l, i) 
  |POr (l, i) -> List.iter (parse_formula f ) l ; f i 
  |PImp (form1, form2, i) 
  |PEquiv (form1, form2, i) -> 
    parse_formula f  form1; parse_formula f  form2; f i 
  |PIte (form1, form2, form3, i) ->  
    parse_formula f  form1; parse_formula f  form2;
    parse_formula f  form3; f i 
  |PForall (vl, form, i) 
  |PExists (vl, form, i)
  |PForall_other (vl, form, i)
  |PExists_other (vl, form, i) ->
    List.iter (fun x -> f x.hstr_i ) vl;
    parse_formula f  form; f i 

let rec parse_pswts f  p =  
  List.iter (fun x -> 
    parse_formula f  x.pup_form ;
    parse_term f  x.pup_t;
    f x.pup_i ) p

let rec parse_pupds f  p = function 
  |None -> let (x, _) =  p.pup_swts in  parse_pswts f  x ;f p.pup_loc  
  |Some(_) -> f p.pup_loc 

let parse_nondets f  n = 
  f n.n_n.hstr_i ;
  f n.n_i 

let parse_assigns f  a = 
  f a.a_n.hstr_i ;
  match a.a_p with
    |PUTerm(_, i)
    |PUCase(_, i) -> f i ;
      f a.a_i 
        


let parse_ptrans f   t =
  f t.ptr_name.hstr_i ;
  parse_formula f  t.ptr_reqs.r_f ;
  List.iter (fun x -> f x.hstr_i ) t.ptr_args;
  List.iter (fun n ->  f n.n_n.hstr_i ; f n.n_i ) t.ptr_s.ptr_nondets;
  List.iter (parse_assigns f ) t.ptr_s.ptr_assigns;
  List.iter (fun x ->
    let (_, i) = x.pup_swts in
    let (p_arg, parg_i) = x.pup_arg in
    if x.pup_info <> None then
      f i  ; f x.pup_arr.hstr_i ;
    (List.iter (fun x -> f x.hstr_i ) p_arg); f parg_i ;
    parse_pupds f  x x.pup_info)
    t.ptr_s.ptr_upds.t_pup_l;
  f t.ptr_s.ptr_upds.t_pup_i ; f t.ptr_s.ptr_i ;  f t.ptr_loc 
    
    
let parse_pform f   p = 
  let (x, vl, form) =  p in 
  parse_formula f  form;
  List.iter (fun x -> f x.hstr_i ) vl ;
  f x 
    
let parse_pform_rev f   p = 
  let (x, vl, form) =  p in 
  f x ;
  List.iter (fun x -> f x.hstr_i ) vl ;
  parse_formula f  form
    
let parse_type_defs f  t =
  let (inf, (name, l)) = t in
  List.iter (fun x -> f x.hstr_i ) l;
  f name.hstr_i ;
  f  inf 
    
let parse_type_defs_rev f  t =
  let (inf, (name, l)) = t in
  f  inf ;
  f name.hstr_i ;
  List.iter (fun x -> f x.hstr_i ) l
    
let parse_glob_const f  x =
  let (i, h, t) = x in 
  f h.hstr_i ;
  f t.hstr_i ;
  f i 
    
let parse_glob_const_rev f  x =
  let (i, h, t) = x in 
  f i ;
  f t.hstr_i ;
  f h.hstr_i 
    
let parse_array f   x =
  let (i, h, (l, t)) = x in 
  f h.hstr_i ;
  List.iter (fun x -> f x.hstr_i ) l;
  f t.hstr_i ;
  f i  
    
let parse_array_rev f   x =
  let (i, h, (l, t)) = x in 
  f i ;
  f t.hstr_i ;
  List.iter (fun x -> f x.hstr_i ) l;
  f h.hstr_i 
    

let parse_linact p  = 
  inact_l := [];
  let f = build_inact in 
  try 
    List.iter (parse_glob_const f ) p.pglobals;
    List.iter (parse_glob_const f ) p.pconsts;
    List.iter (parse_array f ) p.parrays;
    List.iter (parse_type_defs f ) p.ptype_defs;
    parse_pform f  p.pinit;
    List.iter (parse_pform f ) p.pinvs;
    List.iter (parse_pform f ) p.punsafe;
    List.iter (parse_ptrans f ) p.ptrans;
  with Found -> ()


let compare_button_press2 p   =
  match !last_visited with
    |None -> ()
    |Some (inf, _, _)->
      let start_loc, stop_loc = inf.loc in
      (* if not inf.active then      *)
      (*   (tag_list := (UndoComment, start_loc.pos_cnum, stop_loc.pos_cnum)::!tag_list; *)
      (*    inf.active <- not (inf.active); *)
      (*    last_visited := None) *)
      (* else  *)
        (parse_linact p ;
         if 
           (List.exists (fun (x,y) -> 
             start_loc.pos_cnum >= x && stop_loc.pos_cnum <= y) (!inact_l)) = true 
         then raise ParseRev
         else 
           tag_list := (Comment, start_loc.pos_cnum, stop_loc.pos_cnum)::!tag_list;
         inf.active <- not (inf.active);
         inact_l := (start_loc.pos_cnum, stop_loc.pos_cnum)::(!inact_l);
         last_visited := None)

let parse f p  = 
  try 
    List.iter (parse_glob_const f  ) p.pglobals;
    List.iter (parse_glob_const f  ) p.pconsts;
    List.iter (fun (x, _, _) -> f x ) p.pconsts;
    List.iter (parse_array f  ) p.parrays;
    List.iter (parse_type_defs f  ) p.ptype_defs;
    parse_pform f  p.pinit;
    List.iter (parse_pform f  ) p.pinvs;
    List.iter (parse_pform f  ) p.punsafe;
    List.iter (fun x -> parse_ptrans f  x) p.ptrans;
  with Found -> ()
    
let parse_tag p = 
  parse (parse_show_tag) p 

let parse_psystem p = 
  tag_list := [];
  parse compare_motion p ;
  parse_tag p ;
  !tag_list
    
let parse_psystem_m p = 
  tag_list := [];
  try
    compare_button_press2 p ;
    !tag_list
  with ParseRev -> ( tag_list := [];
                     parse_rev compare_button_press p; !tag_list )
    
