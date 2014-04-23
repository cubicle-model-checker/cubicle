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
open Ast
open Types
open Options


type node_info = Empty | Empty_C | Tag | Full

let display_node_contents =
  match dot_level with
  | 0 -> Empty
  | 1 -> Empty_C
  | 2 -> Tag
  | 3 | 5 -> Full
  | _ -> Tag

let display_fixpoints = dot_level >= 4

(* Shape and color configurations for displaying nodes *)

let config = function
  | Orig ->  
     " , color = red, fontcolor=white, fontsize=20, shape=octagon, style=filled"
  | Approx ->
     " , color = blue, shape=rectangle, fontcolor=white, fontsize=20, style=filled"
  | Inv ->
     " , color = orange, shape=rectangle, fontcolor=white, fontsize=20, style=filled"
  | Node -> 
     match display_node_contents with
     | Empty | Empty_C ->  " , shape=point"
     | _ ->  ""

let config_subsumed = " , color = gray, fontcolor=gray"

let config_init =
  " , color = green, fontsize=20, shape=doublecircle, style=filled"

let config_error = ", color=red, fillcolor=lightpink, style=filled"


(* Shape and color configurations for displaying edges *)

let cedge_subsume =
  "style=dashed, arrowhead=onormal, color=gray, constraint=false"

let cedge_candidate =
  "style=dashed, arrowhead=onormal, color=blue, penwidth=4"

let cedge_pre =
  if dot_level = 0 then
    "label=\"\", arrowhead=none, penwidth=1"
  else
    "penwidth=2"

let cedge_error = "color=red, dir=back, pencolor=red, fontcolor=red, penwidth=4"


let rec print_atoms fmt = function
  | [] -> ()
  | [a] -> Atom.print fmt a
  | a::l -> fprintf fmt "%a\\n%a" Atom.print a print_atoms l

let print_cube fmt c =
  fprintf fmt "%a" print_atoms (SAtom.elements c.Cube.litterals)

let print_node_info fmt s = match display_node_contents with
  | Empty -> if s.kind = Orig then fprintf fmt "%d" s.tag
  | Empty_C -> if s.from = [] then print_cube fmt s.cube
  | Tag ->
      if s.from = [] then print_cube fmt s.cube
      else fprintf fmt "%d" s.tag
  | Full -> print_cube fmt s.cube


let print_node_c confstr fmt s =
  fprintf fmt "%d [label=\"%a\"%s]" s.tag print_node_info s confstr

let print_node fmt s = print_node_c (config s.kind) fmt s

let print_subsumed_node fmt s = 
  print_node_c config_subsumed fmt s
      
let print_init_node fmt s = print_node_c config_init fmt s


let print_pre cedge fmt n =
  match n.from with
  | [] -> ()
  | (tr, args, father) :: _ ->
    (* if cedge = cedge_error then *)
    (*  fprintf fmt "%d -> %d [label=\"%a(%a)\", %s]@."  *)
    (*          father.tag n.tag Hstring.print tr.tr_name *)
    (*          Variable.print_vars args *)
    (*          cedge *)
    (*  else *)
     fprintf fmt "%d -> %d [label=\"%a(%a)\", %s]@." 
             father.tag n.tag Hstring.print tr.tr_name
             Variable.print_vars args
             cedge


(* Exported functions *)

let dot_fmt = ref std_formatter

let new_node n =
  fprintf !dot_fmt "%a@." print_node n;
  print_pre cedge_pre !dot_fmt n


let fixpoint s db =
  if display_fixpoints then
    begin
      fprintf !dot_fmt "%a@." print_subsumed_node s;
      print_pre "" !dot_fmt s;
      List.iter (fun d -> 
                 if d <> s.tag then
                   fprintf !dot_fmt "%d -> %d [%s]@." s.tag d cedge_subsume) db
    end
    
let candidate n cand =
  fprintf !dot_fmt "%a@." print_node cand;
  fprintf !dot_fmt "%d -> %d [%s]@." n.tag cand.tag cedge_candidate


let error_trace faulty =
  fprintf !dot_fmt "%a@." print_init_node faulty;
  print_pre cedge_error !dot_fmt faulty;
  (* let prev = ref faulty.tag in *)
  List.iter
    (fun (_, _, s) ->
     print_pre cedge_error !dot_fmt s;
     (* fprintf !dot_fmt "%d -> %d [%s]@." !prev s.tag cedge_error; *)
     (* prev := s.tag; *)
     if s.kind = Node then
       fprintf !dot_fmt "%a@." (print_node_c config_error) s
    ) faulty.from



let dot_header = 
  let run = ref 0 in
  let name = Filename.basename file in
  fun fmt ->
  incr run;
  fprintf fmt "subgraph cluster_%d {@." !run;
          fprintf fmt "	label=\"run %d of %s\";@." !run name

let dot_footer fmt = fprintf fmt "}@."


let restart () =
  dot_footer !dot_fmt;
  fprintf !dot_fmt "\n@.";
  dot_header !dot_fmt


let display_graph dot_file =
  let pdf = dot_file^".pdf" in
  let com = match Util.syscall "uname" with
    | "Darwin\n" -> "open"
    | "Linux\n" -> "xdg-open"
    | _ -> (* Windows *) "cmd /c start"
  in
  match Sys.command ("dot -Tpdf "^dot_file^" > "^pdf^" && "^com^" "^pdf) with
  | 0 -> ()
  | _ ->
     eprintf "There was an error with dot. Make sure graphviz is installed."


let open_dot () =
  if not dot then fun () -> ()
  else
    let bfile = Filename.basename file in
    let dot_file, dot_channel =
      Filename.open_temp_file bfile ".dot" in
    dot_fmt := formatter_of_out_channel dot_channel;
    fprintf !dot_fmt "digraph \"%s\" {@." bfile;
    fprintf !dot_fmt "orientation = portrait;\n\
                      fontsize = 10;\n\
                      rankdir = BT;\n\
                      node [fontname=helvetica];\n\
                      edge [fontname=helvetica];\n\
                      graph [fontname=helvetica];\n\
                      ratio=\"fill\";\n\
                      size=\"11.7,8.3!\";\n\
                      margin=0;\n\
                      splines=polyline;\n\
                      concentrate=false;\n@.";
    dot_header !dot_fmt;
    fun () ->
      dot_footer !dot_fmt;
      dot_footer !dot_fmt;
      close_out dot_channel;
      display_graph dot_file
