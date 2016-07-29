open Psystem_parser
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

let last_hover : int option ref = ref None

(* let last_search_iter = ref None  *)

(* let trans_args = ref [] *)

let kill_thread = ref false

let commented_l  = Hashtbl.create 1000 

(* module M = Map.Make (String) *)

(* let var_map = ref M.empty  *)

let get_storage () = 
  match Js.Optdef.to_option Dom_html.window##localStorage with
  | None -> (Firebug.console##log (Js.string "storage not found") ; raise Not_found)
  | Some t -> t 

let add_hover_marker i j k l  = 
  Js.Unsafe.fun_call (Js.Unsafe.js_expr "add_hover_marker") 
    [|Js.Unsafe.inject i; Js.Unsafe.inject j;Js.Unsafe.inject k;Js.Unsafe.inject l|] 

let add_select_marker i j k l  = 
  Js.Unsafe.fun_call (Js.Unsafe.js_expr "add_select_marker") 
    [|Js.Unsafe.inject i; Js.Unsafe.inject j;Js.Unsafe.inject k;Js.Unsafe.inject l|] 
    
let remove_marker id =   Js.Unsafe.fun_call (Js.Unsafe.js_expr "remove_marker") 
  [|Js.Unsafe.inject id|] 

let list_to_string l  =  
  List.fold_right (fun x acc -> acc ^ x ^ "\n") l ""

let get_mouse_coordinates e =
  e##getDocumentPosition()

(** Envoie a Psystem_parser la position courante du curseur dans le buffer *)
let get_buffer_coordinates d e  = 
  let pos = get_mouse_coordinates e in 
  buffer_l := 0;
  buffer_c := d##positionToIndex (pos, 0)
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
    let (startl, startc) = 
      let pos = d##indexToPosition (start, 0) in 
      pos##row, pos##column in 
    let (stopl, stopc) = 
      let pos = d##indexToPosition (stop, 0) in 
      pos##row, pos##column in 
    (match t_id with 
      |Comment ->  
        let mid = add_select_marker startl startc stopl stopc in 
        Hashtbl.add commented_l (start, stop) mid
      |Hover -> 
        (match !last_hover with 
          |None -> ()
          |Some id -> remove_marker id);
        let mid = add_hover_marker startl startc stopl stopc in 
        last_hover := Some mid
      |UndoComment -> 
        let mid = Hashtbl.find commented_l (start, stop) in 
        remove_marker (mid);
        Hashtbl.remove commented_l (start, stop)
      |UndoHover -> ()
      |Var -> ()
    );
    apply_tag d s

(** Parcourt l'AST pour trouver dans les bornes de quelle loc se trouve le curseur *)
let find_in_ast s editor session document m  = 
  (* if !edit then  *)
  (*   false *)
  (* else  *)
  try
    get_buffer_coordinates document m;
    apply_tag document (parse_psystem !s);
    false
  with CursorNotOverText  -> (apply_tag document (cancel_last_visited ()); false)

(** Appelé après un clic de souris pour commenter *)
let modify_ast ast editor session document b = 
  (* if !edit then false *)
  (*   else  *)
  (*     if (GdkEvent.Button.button b) = 3 && !buffer_l <> -1 && !buffer_c <> -1 then  *)
  (* (apply_tag (parse_var !ast); true) *)
  (*     else  *)
  (*       (if !buffer_l <> -1 && !buffer_c <> -1 then *)
  (* begin *)
  apply_tag document (parse_psystem_m !ast);
    let e2 = Js.Unsafe.variable "editor2" in 
    e2##setValue(Js.string (
      Psystem_printer.psystem_to_string !ast), 1)
(* source2#source_buffer#set_text (Psystem_printer.psystem_to_string !ast) *)
(*           end; *)
(*        true) *)



(** Coordonées fichier sauvegarde session *)
let rec list_position l = 
  match l with 
    |[] |_::[] -> []
    |x::y::s -> (int_of_string x, int_of_string y)::list_position s


let onload s ev =
  (* let mid = add_select_marker (0,0,0,7) in  *)
  (* remove_marker (mid) *)
  let ast = ref s in
  let e = Js.Unsafe.variable "editor1" in
  let session = e##getSession () in
  let d = session##getDocument () in
  e##on("mousemove", (fun ev ->
    find_in_ast ast e session d ev));
  e##on("click", (fun ev ->
    modify_ast ast e session d ev));
  let e2 = Js.Unsafe.variable "editor2" in
  let input_str = e2##getValue() in 
  let buttonEd = Dom_html.getElementById "display-trace" in
  let buttond =
    match Js.Opt.to_option (Dom_html.CoerceTo.button buttonEd) with
      |None -> failwith "button display trace not found"
      |Some b -> b in
  buttond##onclick <- Dom.handler (fun _ ->
    let l = get_storage () in 
    l##clear();
    Firebug.console##log (Js.string "unsafe number");
    l##setItem (Js.string("cub_unsafe"),
                Js.string (string_of_int (punsafe_length !ast)));
    Main.main input_str true; Js._false);
  let buttonEr = Dom_html.getElementById "run-cubicle" in
  let buttonr =
    match Js.Opt.to_option (Dom_html.CoerceTo.button buttonEr) with
      |None -> failwith "button display trace not found"
      |Some b -> b in
  buttonr##onclick <- Dom.handler (fun _ ->
    Main.main input_str false; Js._false)
(* Js._false); *)

    
    
let _ =
  let e = Js.Unsafe.variable "editor1" in 
  (* e##setReadOnly(Js.bool true); *)
  e##setFontSize (14);
  let e2 = Js.Unsafe.variable "editor2" in 
  (* e2##setReadOnly(Js.bool true); *)
  e2##setFontSize (14);
  let str = 
"type req = Empty | Reqs | Reqe | Inv | Invack
type cstate = Invalid | Shared | Exclusive

var Exgntd : bool
var Curcmd : req
var Curptr : proc

array Cache[proc] : cstate
array Shrset[proc] : bool
array Chan[proc] : req

init (z) { Cache[z] = Invalid && Shrset[z] = False &&
           Exgntd = False && Curcmd = Empty && Chan[z]=Empty }

(*
invariant (z) { Cache[z] = Exclusive && Exgntd  = False }
invariant (z) { Cache[z] = Shared && Shrset[z] = False }
*)

unsafe (z1 z2) { Cache[z1] = Exclusive && Cache[z2] = Shared }

transition send_shared (n)
requires { Chan[n] = Empty && Cache[n] = Invalid }
{ 
  Chan[j] := case 
  	      | j = n : Reqs 
	      | _ : Chan[j] 
}

transition recv_shared (n)
requires { Curcmd = Empty && Chan[n] = Reqs }
{ 
  Curcmd := Reqs; 
  Curptr := n ;
  Chan[j] := case
  	      | j = n : Empty 
	      | _ : Chan[j] 
}
    
transition send_exclusive (n)
requires { Chan[n] = Empty && Cache[n] <> Exclusive }
{ 
  Chan[j] := case 
  	      | j = n : Reqe 
	      | _ : Chan[j] 
}

transition recv_exclusive (n)
requires { Curcmd = Empty && Chan[n] = Reqe }
{ 
  Curcmd := Reqe; 
  Curptr := n ;
  Chan[j] := case 
  	      | j = n : Empty 
	      | _ : Chan[j] 
}
    
transition sendinv_1 (n)
requires { Chan[n] = Empty && Shrset[n]=True  &&  Curcmd = Reqe }
{ 
  Chan[j] := case 
  	      | j = n : Inv 
	      | _ : Chan[j] 
}

transition sendinv_2 (n)
requires { Chan[n] = Empty && Shrset[n]=True  &&
	   Curcmd = Reqs && Exgntd=True }
{ 
  Chan[j] := case 
  	      | j = n : Inv 
	      | _ : Chan[j] 
}

transition recv_inv(n)
requires { Chan[n] = Inv }
{ 
  Chan[j] := case 
  	      | j = n : Invack 
	      | _ : Chan[j] ;
  Cache[j] := case 
  	       | j = n : Invalid 
	       | _ : Cache[j] 
}
    
transition recv_invack(n)
requires { Chan[n] = Invack && Curcmd <> Empty }
{ 
  Exgntd := False;
  Chan[j] := case
  	      | j = n : Empty 
	      | _ : Chan[j] ;
  Shrset[j] := case 
  	        | j = n : False 
		| _ : Shrset[j] 
}

transition gnt_shared (n)
requires { Curptr = n && Curcmd = Reqs && Exgntd = False }
{ 
  Curcmd := Empty;
  Shrset[j] := case 
  	       	| j = n : True 
		| _ : Shrset[j];
  Cache[j] := case 
  	       | j = n : Shared 
	       | _ : Cache[j] 
}

transition gnt_exclusive (n)
requires { Shrset[n] = False && Curcmd = Reqe && Exgntd = False && Curptr = n &&
	   forall_other l. Shrset[l] = False }
{ 
  Curcmd := Empty; 
  Exgntd := True;
  Shrset[j] := case
  	        | j = n : True 
		| _ : Shrset[j];
  Cache[j] := case 
  	       | j = n : Exclusive 
	       | _ : Cache[j] 
}
" 

  in

  let str = 
"(* unsafe : t8 -> t1 -> unsafe *)

var A : int 
var B : int
var C : int
var D : int
var E : int
var F : int
var G : int

init () { A = 0 && B = 0 && C = 0 && D = 0 && E = 0 &&
          1 <= F && 1 <= G } 

unsafe (z) { A = 0 && B = 0 && D = 0 && E = 0 && F = 0 }
unsafe (z) { B = 0 && D = 0 && E = 0 && F = 0 && G = 0 }

transition t1 ()
requires { 1 <= F}
 { A := A + 1; F := F - 1; } 

transition t2 ()
requires { A = 1 && 1 <= G }
 { A := A - 1; B := B + 1; G := G - 1; }

transition t3 ()
requires { 1 <= B}
 { B := B - 1; C := C + 1; F := F + 1; }

transition t4 ()
requires { 1 <= C && 1 <= F } 
 { C := C - 1; D := D + 1; F := F - 1; }

transition t5 ()
requires { 1 <= D }
 { D := D - 1; E := E + 1; G := G + 1; }

transition t6 ()
requires { 1 <= E }
 { E := E - 1; F := F + 1; }

transition t7 ()
requires { 1 <= A && 1 <= G }
 { A := A - 1; C := C + 1; F := F + 1; G := G - 1; }

transition t8 ()
requires { 1 <= G && 1 <= F }
 { C := C + 1; G := G - 1; }

transition t9 ()
requires { 1 <= C && 1 <= E }
 { C := C - 1; D := D + 1; E := E - 1; }

transition t10 ()
requires { 1 <= C && 1 <= F }
 { C := C - 1; E := E + 1; F := F - 1; G := G + 1 ; }

transition t11 ()
requires { 1 <= C && 1 <= E }
 { C := C - 1; G := G + 1; }

transition t12 ()
requires { 1 <= F && 1 <= G }
 { E := E + 1; F := F - 1; }
 " in
  let str2 = "
var Turn : proc
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


"in
  e##setValue(Js.string str, 1);
  e2##setValue(Js.string str, 1);
  let lb = from_string str in 
  let p =  (Parser.system Lexer.token lb) in
  Dom_html.window##onload <- Dom_html.handler (fun e -> onload p e; Js._false)
