open Graphics
open Maps

(* Library for making petri net *)

(* Graphical Settings *)
let window_size = 600

let state_size  = 50
let state_text_size   = 50
let state_text_space  = 2

let proc_perc   = 80 (* How much percentage of the available space should proc take *)
let proc_space_perc = 50

let trans_size  = 50  
let trans_text_size = 50
let trans_text_space = 2

(* Point of the arrow settings *)
let arrow_size    = 20  (* Length of the pointy bit *)
let arrow_pointy  = 30  (* How pointy is it ?       *)

module Vector =
struct
  type t = { x : int; y : int }

  let add a b = { x = a.x + b.x; y = a.y + b.y }
  let sub a b = { x = a.x - b.x; y = a.y - b.y }

  let mult k a = { x = k* a.x; y = k* a.y }
  let div  k a = { x = a.x /k; y = a.y /k}

  let dot a b     = a.x * b.x + a.y * b.y
  let norm a      = int_of_float (sqrt (float_of_int (dot a a)))
  let normalize a = div (norm a) a
  let setsize   k a = div (norm a) (mult k a)
  let pp a = Format.printf "(%d, %d)" a.x a.y

  let orth v = [| { x = v.y; y = -v.x }  ; {x = -v.y; y=v.x}|]

  let distance a b = Int.abs (a.x - b.x) + Int.abs (a.y - b.y)

  let zero = { x = 0; y = 0 }
end

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
  val set_state_fun       : t -> (int -> string) -> unit

  val get_state_pos       : t -> string -> Vector.t
  val get_state_map       : t -> (string, Vector.t) Hashtbl.t

  val get_trans_table     : t -> (string, string list * Vector.t) Hashtbl.t
  val get_trans_pos       : t -> string -> Vector.t
  val get_trans_repr      : t -> string -> string list
  val get_state_for_proc  : t -> int -> string
  val get_arcs            : t -> arc list
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
      sfp_fun : (int -> string) ref
    }

  exception Unknown_trans of string
  exception Unknown_state of string

  let empty () : t = 
    {
      states  = Hashtbl.create 10;
      trans   = Hashtbl.create 10; 
      arcs    = ref [];
      sfp_fun = ref (fun (x : int) -> "");
    }
 
  let add_state pet sname sp    = Hashtbl.add pet.states sname sp
  let add_trans pet tname tval  = Hashtbl.add pet.trans tname tval
  let add_arc   pet arc         = pet.arcs := arc::!(pet.arcs)

  let set_state_fun pet g = pet.sfp_fun := g
  
  let get_state_pos pet  i = try Hashtbl.find pet.states i with Not_found -> raise (Unknown_state i)
  let get_state_map pet = pet.states

  let get_trans_table pet = pet.trans
  let get_trans_pos   pet tname = try (let (_,p) = Hashtbl.find pet.trans tname in p) with Not_found -> raise (Unknown_trans tname)
  let get_trans_repr  pet tname = try (let (r,_) = Hashtbl.find pet.trans tname in r) with Not_found -> raise (Unknown_trans tname)

  let get_state_for_proc pet p = !(pet.sfp_fun) p
  let get_arcs pet = !(pet.arcs)

end

let petrinstance = ref (Petri.empty ())
let set_petri p  = petrinstance := p
let get_petri () = !petrinstance


let pre_init () = 
    let ws = string_of_int window_size in
    open_graph (" "^ws^"x"^ws);
    auto_synchronize false

let get_pressed_key () = if key_pressed () then Some(read_key ()) else None
let handle_input    () = 
  match get_pressed_key () with
  | Some(c) -> 
      begin match c with
      | ' ' -> Format.printf "Toggled pause. \n%!"; Simulator.toggle_pause ()
      | 'a' -> Format.printf "Taking step back...\n%!"; Simulator.take_step_back ()
      | 'z' -> Format.printf "Taking step forward...\n%!"; Simulator.take_step_forward ()
      | 'r' -> Format.printf "Resetting simulation...\n%!"; Simulator.reset ()
      | c -> Format.printf "Pressed unbound key : '%c'\n%!" c 
      end
  | _ -> ()

let update dt  = (* Automatically manage pausing and navigating through the trace. *)
  handle_input ()

let draw_for_state () =
  clear_graph ();

  let pet = get_petri () in
  let sttable = Petri.get_state_map pet   in
  let trtable = Petri.get_trans_table pet in

  let draw_arc a =
    let draw_arrow (from : Vector.t) (toward : Vector.t) = 
      let a = Vector.setsize arrow_pointy (Vector.sub from toward) in
      let draw_pointy pointy = 
          let o = Vector.add toward (Vector.setsize arrow_size pointy) in
          let o = Vector.add a o in
          moveto toward.x toward.y;
          lineto o.x o.y;
        in
        moveto from.x from.y;
        lineto toward.x toward.y;
        let ort = Vector.orth (Vector.sub toward from) in
        draw_pointy (ort.(0));
        draw_pointy (ort.(1));
      in

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
  List.iter draw_arc (Petri.get_arcs (get_petri ())); 

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
    fill_rect (x-ts) (y-ts) trans_size trans_size;
    let (tsx, tsy) = text_size trans_name in
    let nx = x - (tsx / 2) in
    let ny = y + tsy - trans_size - trans_text_space in
    moveto nx ny;
    draw_string trans_name
  in
  
  Hashtbl.iter draw_trans trtable;
  set_color black;

  synchronize ()
