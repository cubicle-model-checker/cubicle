(**************************************************************************)
(*                                                                        *)
(*  Ocamlgraph: a generic graph library for OCaml                         *)
(*  Copyright (C) 2004-2010                                               *)
(*  Sylvain Conchon, Jean-Christophe Filliatre and Julien Signoles        *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* This file is a contribution of Benjamin Vadon *)

open Graph
open Ed_hyper

exception Diff_Node of string

type visibility = Visible | BorderNode | Hidden

type label_t = Num_Label | Str_Label 

type mode = 
  | Normal        | Focused
  | Selected      | Selected_Focused 
  | Unsafe        | Unsafe_Focused 
  | VarChange     | VarChange_Focused
  | VarInit       | VarInit_Focused 
  | HighlightPath | HighlightPath_Focused 
  | Path

module Var_Map = Map.Make(String)


type node_info = 
  { 
    mutable label : string;
    mutable label_mode : label_t;
    mutable changed : bool;
    mutable var_map : string Var_Map.t;
    mutable draw : bool;
    mutable str_label : string;
    mutable num_label : string;
    mutable visible : visibility;
    mutable successors_visible : bool;
    mutable depth : int;
    mutable vertex_mode : mode;
    mutable turtle : turtle;
  }

let make_node_info n s d = 
  { 
    str_label = s;
    num_label = n;
    changed = false;
    var_map = Var_Map.empty;
    draw = true;
    label_mode = Num_Label;
    label = n; 
    visible = Hidden; 
    depth = 0; 
    vertex_mode = Normal;
    successors_visible = true;
    turtle = dummy_turtle 
  }

type edge_info = 
  {
    mutable label : string;
    mem_label : string ;
    mutable draw : bool;
    mutable visible_label : bool;
    mutable visited : bool;
    mutable edge_mode : mode;
    mutable edge_turtle : turtle;
    mutable edge_distance : float;
    mutable edge_steps : int;
  }

let make_edge_info () =
  { 
    label = "";
    mem_label = "";
    draw = true;
    visible_label = false;
    visited = false; 
    edge_mode = Normal;
    edge_turtle = dummy_turtle; 
    edge_distance = 0.; 
    edge_steps = 0; 
  }

let make_edge_info_label s d =
  { 
    visible_label = false;
    label = s;
    mem_label = s;
    draw = d;
    visited = false; 
    edge_mode = Normal;
    edge_turtle = dummy_turtle; 
    edge_distance = 0.; 
    edge_steps = 0; 
  }




module EDGE = struct
  type t = edge_info
  let compare : t -> t -> int = Pervasives.compare
  let default = make_edge_info ()
end

module G = 
  Imperative.Digraph.AbstractLabeled(struct type t = node_info end)(EDGE)

module B = Builder.I(G)
 


(* current graph *) 
let graph = ref (G.create ())

let new_graph () = 
  graph := (G.create ())

type name = string option

let graph_name = ref (None: name)

(* useful functions for vertex and edge *)
let string_of_label x = (G.V.label x).label
let get_str_label x = (G.V.label x).str_label 

let edge v w = G.mem_edge !graph v w || G.mem_edge !graph w v 


module Components = Components.Make(G)
module Dfs = Traverse.Dfs(G)

exception Choose of G.V.t

let choose_root () =
  try
    G.iter_vertex (fun v -> raise (Choose v)) !graph;
    None
  with Choose v ->
    Some v


let dfs = ref false

let refresh_rate = ref 10

let aa = ref true

module H2 = 
  Hashtbl.Make
    (struct 
      type t = G.V.t * G.V.t
      let hash (v,w) = Hashtbl.hash (G.V.hash v, G.V.hash w)
      let equal (v1,w1) (v2,w2) = G.V.equal v1 v2 && G.V.equal w1 w2 
    end)

module H = Hashtbl.Make(G.V)

(*  vertex select and unselect *)

(* a counter for selected vertices *)
let nb_selected = ref 0

(* a belonging test to selection *)
let is_selected (x:G.V.t) = 
  let mode =(G.V.label x).vertex_mode in
  mode = Selected ||
  mode = Selected_Focused

type mode_select_list  =  
    REMOVE_FROM of G.V.t 
  | ADD_FROM of G.V.t 
  | NONE


let selected_list mode  =
  let vertex_selection =ref [] in
  G.iter_vertex (fun v -> 
      if (is_selected v) 
      && (match mode with
          | ADD_FROM  vertex -> not (edge v vertex)
          | REMOVE_FROM vertex -> (edge v vertex)
          | NONE -> true)
      then vertex_selection := v::(!vertex_selection)) !graph;
  let compare s1 s2 = String.compare (string_of_label s1) (string_of_label s2) in
  List.sort compare !vertex_selection

type ed_event = Select | Unselect | Focus | Unfocus

let update_vertex vertex event =
  let vertex_info = G.V.label vertex in
  begin
    match vertex_info.vertex_mode, event with
    | Normal, Select -> vertex_info.vertex_mode <- Selected; incr nb_selected
    | Normal, Focus -> vertex_info.vertex_mode <- Focused
    | Normal, _ -> ()
    | Selected, Focus -> vertex_info.vertex_mode <- Selected_Focused
    | Selected, Unselect -> vertex_info.vertex_mode <- Normal; decr nb_selected
    | Selected, _ -> ()
    | Focused, Select -> vertex_info.vertex_mode <- Selected_Focused; incr nb_selected
    | Focused, Unfocus -> vertex_info.vertex_mode <- Normal
    | Focused, _ -> ()
    | Selected_Focused, Unselect -> vertex_info.vertex_mode <- Focused; decr nb_selected
    | Selected_Focused, Unfocus -> vertex_info.vertex_mode <- Selected
    | Selected_Focused, _ -> ()
    | Unsafe, Focus -> vertex_info.vertex_mode <- Unsafe_Focused 
    | Unsafe, _ -> () 
    | Unsafe_Focused, Unfocus -> vertex_info.vertex_mode <- Unsafe
    | Unsafe_Focused, _ -> ()
    | VarChange, Focus -> vertex_info.vertex_mode <- VarChange_Focused
    | VarChange, _ -> ()
    | VarChange_Focused, Unfocus -> vertex_info.vertex_mode <- VarChange
    | VarChange_Focused, _ -> ()
    | _ -> ()
      

  end;
  G.iter_succ_e
    ( fun edge ->
        let edge_info = G.E.label edge in
        let dest_vertex = G.E.dst edge in 
        begin match  edge_info.edge_mode, event with
          | Normal, Select -> edge_info.edge_mode <- Selected
          | Normal, Focus -> edge_info.edge_mode <- Focused
          | Normal, _ -> ()
          | Selected, Focus -> edge_info.edge_mode <- Selected_Focused
          | Selected, Unselect -> if not(is_selected dest_vertex) then edge_info.edge_mode <- Normal
          | Selected, _ -> ()
          | Focused, Select -> edge_info.edge_mode <- Selected_Focused
          | Focused, Unfocus -> edge_info.edge_mode <- Normal
          | Focused, _ -> ()
          | Selected_Focused, Unselect -> if not(is_selected dest_vertex) then edge_info.edge_mode <- Focused; decr nb_selected
          | Selected_Focused, Unfocus -> edge_info.edge_mode <- Selected
          | Selected_Focused, _ -> ()
          | HighlightPath, Focus -> edge_info.edge_mode <- HighlightPath_Focused
          | HighlightPath, _ -> ()
          | HighlightPath_Focused, Unfocus -> edge_info.edge_mode <- HighlightPath
          | HighlightPath_Focused, _  -> ()
          | _ , _ -> () 
        end;       
    ) !graph vertex


(* to select and unselect all vertices *)

let select_all () =  
  G.iter_vertex (fun v -> 
      if not(is_selected v) 
      then begin 
        let v = G.V.label v in
        v.vertex_mode <- Selected;
        incr nb_selected 
      end
    ) !graph;
  G.iter_edges_e (fun e -> let e = G.E.label e in e.edge_mode <- Selected) !graph

let unselect_all () =  
  G.iter_vertex (fun v -> 
      if (is_selected v)
      then begin 
        let l = G.V.label v in
        l.vertex_mode <- Normal;
        decr nb_selected 
      end
    ) !graph;

  G.iter_edges_e (fun e -> let e = G.E.label e in e.edge_mode <- Normal) !graph
  
let find_nodes l  =
  G.fold_vertex (fun v acc ->
    try 
      List.iter (fun (x, var_i) ->
        try
          let var_val = Var_Map.find x (G.V.label v).var_map in
            if not (List.mem var_val var_i) then 
              raise (Diff_Node(x))
        with Not_found -> raise (Diff_Node(x))) l;
      v::acc
    with Diff_Node(x) -> acc) !graph []

let mode_node v m =
  try 
    List.iter (fun (x, var_i) ->
      try
        let var_val = Var_Map.find x (G.V.label v).var_map in
        if not (List.mem var_val var_i) then 
          raise (Diff_Node(x))
      with Not_found -> raise (Diff_Node(x))) m;
    true
  with Diff_Node(x) -> false

let rec get_path dst_mode src_mode acc edge paths =
  let src = G.E.src edge in
  (** Si on trouve un noeud dans l'état scr, on ajoute le chemin à la liste *)
  if mode_node src dst_mode then
    paths := (edge::acc) :: !paths
  else
    (** Sinon on continue jusqu'à trouver la racine ou
        un noeud dans l'état src *)
    let pred_e = G.pred_e !graph src in
    if (G.V.label src).num_label <> "1" then 
      (List.iter (fun e ->
        if mode_node src src_mode then
          get_path dst_mode src_mode [] e paths 
        else
          get_path dst_mode src_mode (edge::acc) e paths) pred_e)

let mode_node v m e =
  let str = ref ((G.E.label e).mem_label ^ "\n") in
  try 
    List.iter (fun (x, var_i) ->
      try
        let var_val = Var_Map.find x (G.V.label v).var_map in
        if not (List.mem var_val var_i) then 
          ( List.iter (fun s -> str := !str ^ x ^ " <- " ^ s) var_i;
           raise (Diff_Node(x)))
      with Not_found -> ()
         (* List.iter (fun s -> str := !str ^ x ^ " <- " ^ s) var_i;  *)
         (* raise (Diff_Node(x)) )*)) m ;
    true
  with Diff_Node(x) -> ((G.E.label e).label <- !str; false)


let rec get_path_to dst_mode acc edge paths = 
  let dst = G.E.dst edge in 
  if not (mode_node dst dst_mode edge) then 
    ((G.E.label edge).edge_mode <- Path;
     paths := (edge::acc) :: !paths)
  else
    let succ_e = G.succ_e !graph dst in 
    if List.length succ_e <> 0 then 
      (List.iter (fun e -> 
        if not (mode_node dst dst_mode e) then 
          ((G.E.label e).edge_mode <- Path; 
           get_path_to dst_mode [] e paths)
        else
          (get_path_to dst_mode (edge::acc) e paths;
           (G.E.label edge).edge_mode <- HighlightPath))) succ_e
    else
      (paths := (edge::acc) :: !paths;
       (G.E.label edge).edge_mode <- Normal)
       
        
