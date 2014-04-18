
let rec print_atom_dot fmt = function
  | True -> fprintf fmt "true"
  | False -> fprintf fmt "false"
  | Comp (x, op, y) -> 
      fprintf fmt "%a %s %a" print_term x (op_comp op) print_term y
  | Ite (la, a1, a2) ->
      fprintf fmt "@[ite(%a,@ %a,@ %a)@]" 
	print_atoms_dot (SAtom.elements la) 
	print_atom_dot a1 print_atom_dot a2

and print_atoms_dot fmt = function
  | [] -> ()
  | [a] -> print_atom_dot fmt a
  | a::l -> fprintf fmt "%a\\n%a" print_atom_dot a print_atoms_dot l

let print_cube_dot fmt sa = 
  fprintf fmt "@[%a@]" print_atoms_dot (SAtom.elements sa)

let print_system_dot fmt s = match verbose with
  | 0 -> ()
  | 1 | 2 ->
      if List.length s.t_from = 0 then print_cube_dot fmt (snd s.t_unsafe)
      else fprintf fmt "%d" s.t_nb
  | _ -> if verbose >= 3 then print_cube_dot fmt (snd s.t_unsafe)


let print_unsafe_dot_node fmt s =
  fprintf fmt
    "%d [label=\"%a\", color = red, fontcolor=white, fontsize=20, shape=octagon, style=filled]"
    s.t_nb print_system_dot s
    
let print_approx_dot_node fmt s =
  fprintf fmt
    "%d [label=\"%a\", color = blue, shape=rectangle, fontcolor=white, fontsize=20, style=filled]"
    s.t_nb print_system_dot s
    
let print_dot_node fmt s =
  fprintf fmt "%d [label=\"%a\"];" s.t_nb print_system_dot s
    
let print_subsumed_dot_node fmt s =
  if verbose > 1 then
    fprintf fmt 
      "%d [label=\"%a\" color = gray, fontcolor=gray];"
      s.t_nb print_system_dot s
      
let print_init_dot_node fmt s =
  fprintf fmt
    "%d [label=\"%a\", color = green, fontsize=20, shape=doublecircle, style=filled]"
    s.t_nb print_system_dot s
    
let print_subsume_dot_arrow fmt a b =
  if verbose > 1 then
    fprintf fmt
      "%d -> %d [style=dashed, arrowhead=onormal, color=gray, constraint=false]@."
      a b

let print_approx_dot_arrow fmt a b =
  fprintf fmt
    "%d -> %d [style=dashed, arrowhead=onormal, color=blue, penwidth=4]@."
    a b
    
let print_pre_dot_arrow fmt s =
  if List.length s.t_from > 0 then
    let (tr, args, _)= List.hd s.t_from in
    fprintf fmt "%d -> %d [label=\"%s(%a)\", penwidth=2];@." 
      s.t_nb_father s.t_nb (Hstring.view tr.tr_name) print_args args

  
let print_buggy_dot_arrow fmt s =
  if List.length s.t_from > 0 then
    fprintf fmt
      "%d -> %d [color=red, constraint=false, dir=back, pencolor=red];@." 
      s.t_nb_father s.t_nb

let print_buggy_dot_node fmt s =
  if s.t_from <> [] then
    fprintf fmt
      "%d [label=\"%a\", color=red, fillcolor=lightpink, style=filled];"
      s.t_nb print_system_dot s

let print_trace_dot fmt s =
  (* print_buggy_dot_arrow fmt s; *)
  List.iter (fun (_, _, s') ->
    (* print_buggy_dot_arrow fmt s'; *)
    print_buggy_dot_node fmt s'
  ) s.t_from 
      
let print_init_dot_node fmt s =
  fprintf fmt
    "%d [label=\"%a\", color = green, fontsize=20, shape=doublecircle, style=filled]"
    s.t_nb print_system_dot s
    
let print_node fmt s =
  if dot then
    begin
      print_pre_dot_arrow fmt s;
      if List.length s.t_from = 0 then
        if s.t_nb >= 0 then print_unsafe_dot_node fmt s
        else print_approx_dot_node fmt s
      else print_dot_node fmt s
    end
  else
    print_trace fmt s

let print_bad fmt s =
  (* fprintf fmt "subgraph cluster_trace {\ *)
  (*       	style=filled; *)
  (*       	color=lightpink;@."; *)
  print_pre_dot_arrow fmt s;
  print_init_dot_node fmt s;
  print_trace_dot fmt s
  (* fprintf fmt "}@." *)
  

let print_subsumed_node appr fmt (s, db) =
  if dot then
    begin
      let db = List.filter (fun x -> x <> s.t_nb) db in
      if verbose > 1 then print_pre_dot_arrow fmt s;
      if s.t_nb = 0 then print_unsafe_dot_node fmt s
      else print_subsumed_dot_node fmt s;
      fprintf fmt "@.";
      if appr then List.iter (print_approx_dot_arrow fmt s.t_nb) db
      else List.iter (print_subsume_dot_arrow fmt s.t_nb) db
    end


let print_dead_node  = print_subsumed_node false

let print_dead_node_to_cand  = print_subsumed_node true

  
let dot_config file cpt_dot =
  if not dot then std_formatter, fun () -> () else       
    begin
      let bfile = Filename.basename file in
      let n, cout = 
	if not profiling then Filename.open_temp_file bfile ".dot" 
	else 
	  begin 
	    incr cpt_dot; 
	    let n = file^(string_of_int !cpt_dot)^".dot" in
	    let cout = open_out n in
	    n, cout
	  end
      in
      let fmt = formatter_of_out_channel cout in
      fprintf fmt "digraph G {@.";
      fprintf fmt "orientation = portrait;@.";
      fprintf fmt "fontsize = 10;@.";
      fprintf fmt "rankdir = BT;@.";
      fprintf fmt "concentrate=true;@.";
      let close_dot () =
	fprintf fmt "}@.";
	if not profiling then
	  let pdf = n^".pdf" in
	  let com = (* find os based on dir structure *)
	    if Sys.file_exists "/System" then "open" (* Mac OS X *)
	    else if Sys.file_exists "/home" then "xdg-open" (* Unix *)
	    else "cmd /c start" (* Windows *)
	  in
	  ignore(Sys.command ("dot -Tpdf "^n^" > "^pdf^" && "^com^" "^pdf))
      in
      fmt, close_dot
    end
