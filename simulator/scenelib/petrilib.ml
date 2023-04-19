(*        Library for making petri net         *)
(* see https://en.wikipedia.org/wiki/Petri_net *)
(*                                             *)

open Bgraphics
open Maps
open Input

(* Graphical Settings *)
let window_size = 600

let state_size        = 50
let state_text_size   = 50
let state_text_space  = 2

let proc_perc       = 80 (* How much percentage of the available space should procs take *)
let proc_space_perc = 50

let trans_size        = 50  
let trans_text_size   = 50
let trans_text_space  = 2

let indic_size        = 50
let indic_text_size   = 50
let indic_text_space  = 2

let button_size         = 50
let button_text_size    = 50

module Petri : sig

  type arc = 
    | TransToState of string * string  (* From transition to state *)
    | StateToTrans of string * string  (* From state to transition *)

  exception Unknown_trans of string
  exception Unknown_state of string

  type t

  val empty               : unit -> t
  val add_state           : t -> string -> Vector.t -> unit
  val add_trans           : t -> string -> (string list * Vector.t) -> unit
  val add_arc             : t -> arc -> unit
  val add_indic           : t -> string -> (unit -> bool) -> Vector.t -> unit
  val add_button          : t -> string -> (unit -> bool) -> Vector.t -> unit

  val set_state_fun       : t -> (int -> string) -> unit

  val get_state_pos       : t -> string -> Vector.t
  val get_state_map       : t -> (string, Vector.t) Hashtbl.t

  val get_trans_table     : t -> (string, string list * Vector.t) Hashtbl.t
  val get_trans_pos       : t -> string -> Vector.t
  val get_trans_repr      : t -> string -> string list
  val get_state_for_proc  : t -> int -> string
  val get_arcs            : t -> arc list
  val get_indics          : t -> (string * (unit -> bool) * Vector.t) list
  val get_buttons         : t -> Button.t list
end
=
struct
  
  type arc = 
  | TransToState of string * string  
  | StateToTrans  of string * string
  type t = 
    { states  : (string, Vector.t) Hashtbl.t;
      trans   : (string, string list * Vector.t) Hashtbl.t;
      arcs    : arc list ref;
      sfp_fun : (int -> string) ref;
      indics  : (string * (unit -> bool) * Vector.t ) list ref;
      buttons : Button.t list ref;
    }

  exception Unknown_trans of string
  exception Unknown_state of string

  let empty () : t = 
    {
      states  = Hashtbl.create 10;
      trans   = Hashtbl.create 10; 
      arcs    = ref [];
      sfp_fun = ref (fun (x : int) -> "");
      indics  = ref [];  
      buttons = ref [];
    }
 
  let add_state pet sname sp    = Hashtbl.add pet.states sname sp
  let add_trans pet tname tval  = Hashtbl.add pet.trans tname tval
  let add_arc   pet arc         = pet.arcs := arc::!(pet.arcs)
  let add_indic pet iname ifun ival   = pet.indics := (iname, ifun, ival)::!(pet.indics)
  let add_button pet name f pos  = 
    let nb : Button.t = 
      {
        name;
        f;
        pos;
        size=button_size;
      } in 
    pet.buttons := nb::!(pet.buttons)

  let set_state_fun pet g = pet.sfp_fun := g
  
  let get_state_pos pet  i = try Hashtbl.find pet.states i with Not_found -> raise (Unknown_state i)
  let get_state_map pet = pet.states

  let get_trans_table pet = pet.trans
  let get_trans_pos   pet tname = try (let (_,p) = Hashtbl.find pet.trans tname in p) with Not_found -> raise (Unknown_trans tname)
  let get_trans_repr  pet tname = try (let (r,_) = Hashtbl.find pet.trans tname in r) with Not_found -> raise (Unknown_trans tname)

  let get_state_for_proc pet p = !(pet.sfp_fun) p
  let get_arcs pet = !(pet.arcs)
  let get_indics pet = !(pet.indics) 
  let get_buttons pet = !(pet.buttons)

end

let petrinstance = ref (Petri.empty ())
let set_petri p  = petrinstance := p
let get_petri () = !petrinstance

(* Dynamic variable, dont touch *)
let last_registered_pos = ref Vector.zero
let mouse_down = ref false
let button_last_result = ref false
let button_clicked = ref false
let mouse_speed = 1

let pre_init () = 
    let ws = string_of_int window_size in
    open_graph (" "^ws^"x"^ws);
    auto_synchronize false

let draw_for_state () =
  clear_graph ();

  let pet = get_petri () in
  let sttable = Petri.get_state_map pet   in
  let trtable = Petri.get_trans_table pet in
  let (mx, my) = mouse_pos () in 
  
  (* Draw arcs *)
  set_color black;
  let draw_arc a =
    let fst, scnd = match a with
    | Petri.StateToTrans(st,tr) -> 
        let (f,s) = (Petri.get_state_pos pet st, Petri.get_trans_pos pet tr)  in
        (* Get on the border of the circle not inside *)
        let diff = Vector.setsize state_size (Vector.sub s f)                 in
        let f = Vector.add diff f in
        (* Get on the border of the square not inside *)
        let diff = Vector.setsize trans_size (Vector.sub f s) in
        let s = Vector.add diff s in 

        f,s
    | Petri.TransToState(tr,st) -> 
        let (f,s) = (Petri.get_trans_pos pet tr, Petri.get_state_pos pet st)  in
        let diff = Vector.setsize state_size (Vector.sub f s)                 in
        f,(Vector.add diff s)
    in
    draw_arrow fst scnd;
  in
  List.iter draw_arc (Petri.get_arcs pet); 


  (* Draw states *)
  set_text_size state_text_size; 
  let draw_state state_id ({x; y} : Vector.t) = 
    set_color black;
    draw_circle x y state_size;
    let proc_in_state = ref [] in
    for i=0 to (Utils.get_nb_proc ()-1) do
      let ps = Petri.get_state_for_proc (get_petri ()) i in
      if ps = state_id then proc_in_state := i::(!proc_in_state)
    done;

    let (tsx, tsy) = text_size state_id in
    let nx = x - (tsx / 2) in
    let ny = y - tsy - state_size - state_text_space in
    moveto nx ny;
    draw_string state_id;

    let nb_proc = List.length (!proc_in_state) in
    if nb_proc > 0 then
      (
        let procs =
          try
            let ((_, proc), _) = Traces.get (Simulator.full_trace) in
            proc
          with Failure(_) -> []
        in
        (* Organize proc in a cell *)
        let row_size = int_of_float (Float.ceil (Float.sqrt (float_of_int nb_proc))) in
        let psize = (proc_perc * state_size) / (row_size * 100) in
        let rpsize = (psize * proc_space_perc) / 100 in
        let cen = if row_size <= 1 then 0 else (row_size * psize) / 4 in
        let xtopleft = x - cen in 
        let ytopleft = y - cen in
        let rpdiv = rpsize / 2 in
        let draw_proc i p =
          let xingrid = i mod row_size in
          let yingrid = i / row_size in
          let rx  = xtopleft + (xingrid*psize) in
          let ry  = ytopleft + (yingrid*psize) in
          let col = if List.mem p procs then red else black in
          set_color col;
          fill_circle rx ry rpsize;
        in
        List.iteri draw_proc (!proc_in_state);
      )
  in
  Hashtbl.iter draw_state sttable;

  (* Draw transitions *)
  let ts = trans_size / 2 in
  set_text_size trans_text_size; 
  let draw_trans trans_name (slist, ({x;y} : Vector.t)) =
    let col =
      try
        let ((t_name, _), _) = Traces.get (Simulator.full_trace) in
        if List.mem t_name slist then red else black
      with Failure(_) -> (black)
    in
    set_color col;
    fill_rect (x - ts) (y - ts) trans_size trans_size;
    let (tsx, tsy) = text_size trans_name in
    let nx = x - (tsx / 2) in
    let ny = y + tsy - trans_size - trans_text_space in
    moveto nx ny;
    draw_string trans_name
  in
  
  Hashtbl.iter draw_trans trtable;
  set_color black;

  (* Draw indicators *)
  let hs = indic_size / 2 in
  let draw_indicator ((name : string), (f : unit -> bool), (pos : Vector.t)) =
    let status = f () in
    let color  = if status then red else black in
    set_color color;
    fill_rect (pos.x - hs) (pos.y - hs) indic_size indic_size;
    let (tsx, tsy) = text_size name in
    let nx = pos.x - (tsx / 2) in
    let ny = pos.y - tsy - indic_size - indic_text_space in
    moveto nx ny;
    draw_string name;
  in

  List.iter draw_indicator (Petri.get_indics pet);
  List.iter Renderer.draw_button (Petri.get_buttons pet);

  if !Simulator.is_paused then
    (
      moveto 5 5;
      draw_string "Paused."
    );

  if Simulator.is_unsafe () then 
    (
      set_color red;
      moveto (size_x () / 2) (size_y () / 2);
      draw_string "UNSAFE!"
    );
  synchronize ()

let update dt  = (* Automatically manage pausing, navigating through the trace, buttons and Camera *)
  Input.update draw_for_state (Petri.get_buttons (get_petri ())) dt
