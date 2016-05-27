open Ast 
open Lexing
open Util
open Types

exception Found
exception Found2


type ast_t = Globals | Consts | Arrays | Invs | Unsafe | Init | TypeDefs | Trans | Upds |
Assigns | Reqs | Nondets


let buffer_l = ref (-1)
let buffer_c = ref (-1)
let last_visited = ref None
  
let compare_location l buffer ty id =
  let start_loc, stop_loc = l.loc in
  let b_l = !buffer_l in
  let b_c = !buffer_c in
  let l_start = start_loc.pos_lnum in
  let c_start =  start_loc.pos_cnum in
  let l_stop = stop_loc.pos_lnum in
  let c_stop =  stop_loc.pos_cnum in
  try
    if l_start == l_stop && l_start == b_l && b_c >= c_start && b_c < c_stop 
      || l_start == b_l && b_c >= c_start ||l_stop == b_l && b_c < c_stop 
      ||  b_l > l_start && b_l < l_stop then
        raise Found
  with Found ->
    let start_iter = buffer#get_iter (`OFFSET c_start) in
    let stop_iter = buffer#get_iter (`OFFSET c_stop) in
      (match !last_visited with
        |None -> ()
        |Some (t, num, start, stop) ->
          if not (t == ty && num == id) then  
            buffer#remove_tag_by_name "gray_background" ~start:start ~stop:stop);
    (if l.active then 
        buffer#apply_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter              else 
        buffer#remove_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter;);
    last_visited := Some (ty, id, start_iter, stop_iter);
    raise Found
          
        
        
let parse_1 g buffer ty  = 
  let rec f g i = 
    try
      match g with 
      |[] -> ()  
      |(l,_,_)::s -> compare_location l buffer ty i ; f s (i + 1)
    with Found  -> ()
  in
  f g 0
    
let parse_2 g buffer ty = 
  let rec f g i = 
    try
      match g with 
      |[] -> ()  
      |(l,_)::s -> compare_location l buffer ty i ; f s (i + 1)
    with Found  -> () 
  in
  f g 0

let parse_upds g buffer ty = 
    let rec f g i = 
      try
        match g with 
          |[] -> ()  
          |x::s -> 
            compare_location x.up_loc buffer ty i ; f s (i + 1)
      with 
          Found -> raise Found2 in
    f g 0

let parse_assigns g buffer ty = 
    let rec f g i = 
      try
        match g with 
          |[] -> ()
          |(_,_,inf)::s -> 
            compare_location inf buffer ty i ;  f s (i + 1)
      with 
          Found -> raise Found2 in
    f g 0


let parse_nondets g buffer ty = 
    let rec f g i = 
      try
        match g with 
          |[] -> ()
          |(_,inf)::s -> 
            compare_location inf buffer ty i ;  f s (i + 1)
      with 
          Found -> raise Found2 in
    f g 0

let parse_3 g buffer ty = 
  let rec f g i = 
      match g with 
        |[] -> ()  
        |x::s ->
          try 
            compare_location x.tr_reqs.r_info buffer Reqs 0 ;
            parse_nondets x.tr_nondets buffer Nondets;
            parse_assigns x.tr_assigns buffer Assigns;
            parse_upds x.tr_upds buffer Upds;
            compare_location x.tr_loc buffer ty i ;
            f s (i + 1)
          with 
            |Found  -> ()
            |Found2 -> ()
  in
  f g 0


  
let modify l buffer ty id =
  let start_loc, stop_loc = l.loc in
  let b_l = !buffer_l in
  let b_c = !buffer_c in
  let l_start = start_loc.pos_lnum in
  let c_start =  start_loc.pos_cnum in
  let l_stop = stop_loc.pos_lnum in
  let c_stop =  stop_loc.pos_cnum in
  try
    if l_start == l_stop && l_start == b_l && b_c >= c_start && b_c < c_stop 
      || l_start == b_l && b_c >= c_start ||l_stop == b_l && b_c < c_stop 
      ||  b_l > l_start && b_l < l_stop then
      raise Found
  with Found ->
    let start_iter = buffer#get_iter (`OFFSET c_start) in
    let stop_iter = buffer#get_iter (`OFFSET c_stop) in
    (if l.active then 
        (buffer#remove_tag_by_name "gray_background" ~start:start_iter ~stop:stop_iter;         buffer#apply_tag_by_name "delete" ~start:start_iter ~stop:stop_iter)
     else 
        (buffer#remove_tag_by_name "delete" ~start:start_iter  ~stop:stop_iter));
    l.active <- not (l.active);
    last_visited := None;
    raise Found
    


          
let parse_m1 g buffer ty  = 
  let rec f g i = 
    try
      match g with 
      |[] -> ()  
      |(l,_,_)::s -> modify l buffer ty i ; f s (i + 1)
    with Found  -> ()
  in
f g 0
    
let parse_m2 g buffer ty = 
  let rec f g i = 
    try
      match g with 
      |[] -> ()  
      |(l,_)::s -> modify l buffer ty i ; f s (i + 1)
    with Found  -> ()
  in
  f g 0
    

let modify_upds g buffer ty = 
    let rec f g i = 
      try
        match g with 
          |[] -> ()  
          |x::s -> 
            modify x.up_loc buffer ty i ; f s (i + 1)
      with 
          Found -> raise Found2 in
    f g 0


let modify_assigns g buffer ty = 
    let rec f g i = 
      try
        match g with 
          |[] -> ()  
          |(_,_,inf)::s -> 
            modify inf buffer ty i ; f s (i + 1)
      with 
          Found -> raise Found2 in
    f g 0

let modify_nondets g buffer ty = 
    let rec f g i = 
      try
        match g with 
          |[] -> ()
          |(_,inf)::s -> 
            modify inf buffer ty i ;  f s (i + 1)
      with 
          Found -> raise Found2 in
    f g 0


let parse_m3 g buffer ty = 
  let rec f g i =

      match g with
        |[] -> ()  
        |x::s ->
          try
            modify x.tr_reqs.r_info buffer Reqs 0 ;
            modify_nondets x.tr_nondets buffer Nondets ;
            modify_assigns x.tr_assigns buffer Assigns;
            modify_upds x.tr_upds buffer Upds ;
            modify x.tr_loc buffer ty i ;
            f s (i + 1)
          with 
            |Found  -> ()
            |Found2 -> f s (i + 1) 
  in
  f g 0

    
let parse_ast s buffer = 
  try
    parse_1 s.globals buffer Globals ;
    parse_1 s.consts buffer Consts ;
    parse_1 s.arrays buffer Arrays ;
    parse_2 s.type_defs buffer TypeDefs ;
    let (l,_,_) = s.init in
    compare_location l buffer Init 0;
    parse_1 s.invs buffer Invs;
    parse_1 s.unsafe buffer Unsafe;
    parse_3 s.trans buffer Trans
  with Found -> ()
 

let parse_modify_ast s buffer = 
  try 
    parse_m1 s.globals buffer Globals ;
    parse_m1 s.consts buffer Consts ;
    parse_m1 s.arrays buffer Arrays ;
    parse_m2 s.type_defs buffer TypeDefs ;
    let (l,_,_) = s.init in
    modify l buffer Init 0;
    parse_m1 s.invs buffer Invs;
    parse_m1 s.unsafe buffer Unsafe;
    parse_m3 s.trans buffer Trans
  with Found -> ()
