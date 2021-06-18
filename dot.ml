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
open Util
open Html

type node_info = Empty | Empty_C | Tag | Full

let graphviz_prog nb = match dot_prog with
  | Dot when nb < 3000 -> "dot"
  | _ ->  "sfdp -Goverlap=prism"

let display_node_contents =
  match dot_level with
  | 0 -> Empty
  | 1 -> Empty_C
  | 2 -> Tag
  | 3 | 5 -> Full
  | _ -> Tag

let display_fixpoints = dot_level >= 4

let splines = if display_fixpoints then "false" else "polyline"

let current_color = ref black

let next_shade = chromatic green magenta Options.dot_colors

(* Shape and color configurations for displaying nodes *)

let config = function
  | Orig ->
     " , color = red, shape=octagon, \
      fontcolor=white, fontsize=20, style=filled, orig=true"
  | Approx ->
     " , color = blue, shape=rectangle, \
      fontcolor=white, fontsize=20, style=filled, approx=true"
  | Inv ->
     " , color = orange, shape=rectangle, \
      fontcolor=white, fontsize=20, style=filled, invariant=true"
  | Node ->
     match display_node_contents with
     | Empty | Empty_C -> 
         sprintf " , shape=point, color=\"%s\", empty=true" (hex_color !current_color)
     | _ -> sprintf "color=\"%s\"" (hex_color !current_color)

let info_sfdp s = match dot_prog with
  | Sfdp -> "label=\" \", "^s
  | _ -> s

let config_subsumed = " , color = gray, fontcolor=gray, subsumed=true"

let config_init =
  " , color = green, fontsize=20, shape=doublecircle, style=filled, unsafe=true"

let config_error = ", color=red, fillcolor=lightpink, style=filled, error=true"


(* Shape and color configurations for displaying edges *)

let cedge_subsume = info_sfdp
  "style=dashed, arrowhead=onormal, color=gray, constraint=false, subsume=true"

let cedge_candidate = info_sfdp
  "style=dashed, arrowhead=onormal, color=blue, penwidth=4, candidate=true"

let cedge_pre () =
  if dot_level <= 1 then
    info_sfdp (sprintf "label=\" \", arrowhead=none, penwidth=2, color=\"%s\""
                       (hex_color !current_color))
  else
    info_sfdp (sprintf "penwidth=2, color=\"%s\""
                       (hex_color !current_color))

let cedge_error ?(to_init=false) () =
  info_sfdp ("color=red, dir=back, pencolor=red, \
              fontcolor=red, penwidth=4, error=true"^
               (if dot_level = 1 || to_init then "" else ", label=\" \""))


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


let nb_nodes = ref 0

let print_node_c confstr fmt s =
  incr nb_nodes;
  fprintf fmt "%d [label=\"%a\"%s]" s.tag print_node_info s confstr

let print_node fmt s = print_node_c (config s.kind) fmt s

let print_subsumed_node fmt s = 
  print_node_c config_subsumed fmt s
      
let print_init_node fmt s = print_node_c config_init fmt s


let print_pre cedge fmt n =
  match n.from with
  | [] -> ()
  | (tr, args, father) :: _ ->
     fprintf fmt "%d -> %d [label=\"%a(%a)\", %s]@." 
             father.tag n.tag Hstring.print tr.tr_name
             Variable.print_vars args
             cedge


(* Exported functions *)

let dot_fmt = ref std_formatter

let new_node n =
  current_color := next_shade ();
  fprintf !dot_fmt "%a@." print_node n;
  print_pre (cedge_pre ()) !dot_fmt n


let fixpoint s db =
  if display_fixpoints then
    begin
      current_color := next_shade ();
      fprintf !dot_fmt "%a@." print_subsumed_node s;
      print_pre (cedge_pre ()^",penwidth=1") !dot_fmt s;
      List.iter (fun d -> 
                 if d <> s.tag then
                   fprintf !dot_fmt "%d -> %d [%s]@." s.tag d cedge_subsume) db
    end
    
let candidate n cand =
  fprintf !dot_fmt "%a@." print_node cand;
  fprintf !dot_fmt "%d -> %d [%s]@." n.tag cand.tag cedge_candidate


let error_trace faulty =
  fprintf !dot_fmt "%a@." print_init_node faulty;
  print_pre (cedge_error ~to_init:true ()) !dot_fmt faulty;
  (* let prev = ref faulty.tag in *)
  List.iter
    (fun (_, _, s) ->
     print_pre (cedge_error ())!dot_fmt s;
     if s.kind = Node then
       fprintf !dot_fmt "%a@." (print_node_c config_error) s
    ) faulty.from


let delete_node_by n p =
  if n.deleted then
    begin
      fprintf !dot_fmt "%d [color=\"blue\"]@." n.tag;
              (* (hex_color !current_color); *)
      (* if Node.has_deleted_ancestor n then match n.from with *)
      (* | (_,_,p)::_ -> *)
         fprintf !dot_fmt "%d -> %d [penwidth=2, color=blue, style=dashed, \
                           constraint=false, arrowhead=onormal]"
           n.tag p.tag 
      (* | _ -> () *)
      (* fprintf !dot_fmt "%d -> %d [style=dashed, constraint=false]" s.tag n.tag *)
    end

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


let display_graph dot_file online =
  let html_file = dot_file^".html" in
  let ic = open_in dot_file in
  let dot_str = try
    let str = really_input_string ic (in_channel_length ic) in
    close_in ic;
    str
  with e ->
    eprintf "There was an error while reading the dot file.";
    close_in_noerr ic;
    raise e
  in
  (if online then
    print_html html_file Js_of_cubicle.online_path dot_str
  else
    match js_of_cubicle with
    | "" -> print_html html_file Js_of_cubicle.local_path dot_str
    | _ as path -> print_html html_file path dot_str);
  let com = match Util.syscall "uname" with
    | "Darwin\n" -> "open"
    | "Linux\n" -> "xdg-open"
    | _ -> (* Windows *) "cmd /c start"
  in
  match Sys.command (com^" "^html_file) with
  | 0 -> ()
  | _ ->
     eprintf "There was an error with dot. Make sure graphviz is installed."


let open_dot () =
  if not dot then fun () -> ()
  else
    let bfile = Filename.basename file in
    let dot_file, dot_channel = (bfile ^ ".dot"), open_out (bfile ^ ".dot") in
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
                      splines=false;\n\
                      concentrate=false;\n@.";
    dot_header !dot_fmt;
    fun () ->
      dot_footer !dot_fmt;
      dot_footer !dot_fmt;
      close_out dot_channel;
      match (html, html_online) with
      | true, _
      | _, true -> display_graph dot_file html_online
      | _ -> ()
