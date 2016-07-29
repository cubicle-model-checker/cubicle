cd open Psystem_parser
open Lexing
open Options
open Format
open Js

class type aceEditor = 
object 
  method getLastVisibleRow : unit Js.t -> Js.number Js.t Js.meth
  method getValue : unit Js.t -> Js.js_string Js.t Js.meth
  method on : Js.js_string Js.t -> (Js.Unsafe.any Js.t -> unit) Js.callback -> unit Js.meth
end

exception CursorNotOverText 
exception FileError
exception KillThread
exception Value_mode_error
exception Match

let last_search_iter = ref None 

let trans_args = ref []

let kill_thread = ref false

let wd = if double then 1600 else 1000

module M = Map.Make (String)

let var_map = ref M.empty 

let add_marker i j k l = 
  Js.Unsafe.fun_call (Js.Unsafe.js_expr "add_marker") 
    [|Js.Unsafe.inject i; Js.Unsafe.inject j;Js.Unsafe.inject k;Js.Unsafe.inject l|] 
    
let remove_maker id =  
  Js.Unsafe.fun_call (Js.Unsafe.js_expr "remove_marker") 
    [|Js.Unsafe.inject id|] 

    
let list_to_string l  =  
  List.fold_right (fun x acc -> acc ^ x ^ "\n") l ""
    

let get_mouse_coordinates e =
  e##getDocumentPosition()

(** Envoie a Psystem_parser la position courante du curseur dans le buffer *)
let get_buffer_coordinates d e = 
  let pos = get_mouse_coordinates e in 
  buffer_l := 0;
  buffer_c := d##positionToIndex (pos)
(* let buffer_x, buffer_y = source#window_to_buffer_coords `TEXT mouse_x mouse_y in  *)
(* let iter = source#get_iter_at_location buffer_x buffer_y in  *)
(* if not iter#inside_sentence then  *)
(*   (buffer_l := -1; *)
(*    buffer_c := -1; *)
(*    raise CursorNotOverText); *)
(* buffer_l := 1 + iter#line;  *)
(* buffer_c := iter#offset *)
    
let rec apply_tag d = function 
  |[] -> ()
  |(t_id, start, stop)::s -> 
    let (startl, startc) = d##indexToPosition (start) in 
    let (stopl, stopc) = d##indexToPostion (stop) in ()
    (* (match t_id with  *)
    (* |Comment ->  () *)
    (*   (\* source#source_buffer#apply_tag_by_name "delete" *\) *)
    (*   (\*   ~start:start_iter ~stop:stop_iter; *\) *)
    (*   (\* source#source_buffer#apply_tag_by_name "dark" *\) *)
    (*   (\*   ~start:start_iter ~stop:stop_iter; *\) *)
    (* |Hover -> add_marker startl startc stopl stopc *)
    (*   (\* source#source_buffer#apply_tag_by_name "gray_background"  *\) *)
    (*   (\*   ~start:start_iter ~stop:stop_iter; apply_tag s *\) *)
    (* |UndoComment -> () *)
    (*   (\* source#source_buffer#remove_tag_by_name "delete" *\) *)
    (*   (\*   ~start:start_iter ~stop:stop_iter; *\) *)
    (*     (\* source#source_buffer#remove_tag_by_name "dark" *\) *)
    (*   (\*   ~start:start_iter ~stop:stop_iter *\) *)
    (* |UndoHover -> () *)
    (*   (\* source#source_buffer#remove_tag_by_name "gray_background"  *\) *)
    (*   (\*   ~start:start_iter ~stop:stop_iter *\) *)
    (* |Var -> () *)
    (* (\* begin *\) *)
    (*     (\*   source#source_buffer#apply_tag_by_name "var" *\) *)
    (* (\*     ~start:start_iter ~stop:stop_iter; *\) *)
    (* (\*   let str =  (source#source_buffer#get_text ~start:start_iter ~stop:stop_iter() ) in *\) *)
    (* (\*   if M.mem str !var_map then  *\) *)
    (* (\*     (let (be, en) = M.find str !var_map in *\) *)
    (*     (\*      if be = start && en = stop then *\) *)
    (* (\*        var_map := M.remove str !var_map ; *\) *)
    (* (\*      source#source_buffer#remove_tag_by_name "var" *\) *)
    (* (\*        ~start:start_iter ~stop:stop_iter) *\) *)
    (* (\*   else  *\) *)
    (* (\*     var_map := M.add str (start, stop) !var_map           *\) *)
    (* (\* end *\) *)
    (* ); *)
    (* apply_tag d s *)
      
(** Parcourt l'AST pour trouver dans les bornes de quelle loc se trouve le curseur *)
let find_in_ast s editor session document m  = 
  if !edit then 
    false
  else 
    try 
      get_buffer_coordinates document m;
      apply_tag document (parse_psystem !s);
      false
    with CursorNotOverText  -> (apply_tag (cancel_last_visited ()); false)

(** Appelé après un clic de souris pour commenter *)
let modify_ast ast editor session document b = 
  if !edit then false
    else 
      if (GdkEvent.Button.button b) = 3 && !buffer_l <> -1 && !buffer_c <> -1 then 
        (apply_tag (parse_var !ast); true)
      else 
        (if !buffer_l <> -1 && !buffer_c <> -1 then
            begin
              apply_tag (parse_psystem_m !ast);
              source2#source_buffer#set_text (Psystem_printer.psystem_to_string !ast)
            end;
         true)




let onload s _  = 
  let ast = ref s in
  let e = Js.Unsafe.variable "editor" in 
  let session = e##getSession () in 
  let d = session##getDocument () in
  e##on("mousemove", (fun e -> 
    find_in_ast ast editor session document))()
    
let _ =
  let e = Js.Unsafe.variable "editor" in 
  let str = 
    "var Turn : proc
array Want[proc] : bool
array Crit[proc] : bool

init (z) { Want[z] = False && Crit[z] = False }

unsafe (z1 z2) { Crit[z1] = True && Crit[z2] = True }

transition req (i)
requires { Want[i] = False }
{ Want[i] := True }

transition enter (i)
requires { Want[i]=True && Crit[i] = False && Turn = i}
{ Crit[i] := True; }

transition exit (i)
requires { Crit[i] = True }
{ 
  Turn := . ;
  Crit[i] := False; 
  Want[i] := False
}
" in
  e##value <- str;
  let lb = from_string str in 
  Dom_html.window##onload <- Dom_html.handler onload (Parser.system Lexer.token lb)
