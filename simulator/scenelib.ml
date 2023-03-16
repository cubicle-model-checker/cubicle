open Graphics
open Maps

(* Library for making petri net *)

(*
  On demande a l'utilisateur de créer un réseau de pétri.
  Pour cela, l'utilisateur entre :
    Places
    Transition
    Arc

  On peut dire qu'il définit :
    Une place (Quel type ?)
    Une fonction qui a un proc associe une place
  OU ALORS
    Une fonction qui pour une  place renvoie les procs qui y appartiennet : Permet plus aisément de décrire les procs
    Et de les afficher correctement et les scales a usein d'un prikc 

  Réglages possible:
    Couleur a donner a un proc (Tous noir, Une certaine couleur si c'était un pion qui a pris une transition au dernier tour, ...)

L'utilisateur veut créer un réseau de pétri.
Il a besoin de définir :
  Un nombre d'état possible
  Une fonction qui a tout proc donne un état
  Des transitions (Simplement des string, doivent correspondre a des transitions cubicle)
  Des arcs, a savoir des flèches qui relient des états a des transition
*)

(* Graphical Settings *)
let window_size = 600
let state_size  = 50
let proc_perc   = 80 (* size taken by proc in perc of state_size *)
let proc_space_perc = 50
let trans_size  = 50


(* Minor settings *)
let arrow_size    = 20
let arrow_pointy  = 30

module Vector =
struct
  type t = { x : int; y : int }

  let add a b = { x = a.x + b.x; y = a.y + b.y }
  let sub a b = { x = a.x - b.x; y = a.y - b.y }

  let mult k a = { x = k* a.x; y = k* a.y }
  let div  k a = { x = a.x /k; y = a.y /k}

  let dot a b = a.x * b.x + a.y * b.y
  let norm a = int_of_float (sqrt (float_of_int (dot a a)))
  let normalize a = div (norm a) a
  let setsize   k a = div (norm a) (mult k a)
  let pp a = Format.printf "(%d, %d)" a.x a.y

  let orth v = [| { x = v.y; y = -v.x }  ; {x = -v.y; y=v.x}|]

  let distance a b = Int.abs (a.x - b.x) + Int.abs (a.y - b.y)

  let zero = { x = 0; y = 0 }
end

(* Petri Settings *)
module Petri : sig
  type arc = 
    | Out of string * int     (* From transition to state *)
    | In  of int    * string  (* From state to transition *)
  
  type t

  val empty               : unit -> t
  val add_state           : t -> (int * Vector.t) -> unit
  val add_trans           : t -> (string * Vector.t) -> unit
  val add_arc             : t -> arc -> unit
  val set_state_fun       : t -> (int -> int) -> unit
  val set_state           : t -> (int * Vector.t) list -> unit

  val get_states          : t -> Vector.t IntMap.t
  val get_trans           : t -> (string,Vector.t) Hashtbl.t
  val get_state_for_proc  : t -> int -> int
  val get_arcs            : t -> arc list
end
=
struct
  
  type arc = 
  | Out of string * int     
  | In  of int    * string
  (* Place, Place_pos; Transition, Transition_pos; Arcs ; place_id -> proc on this place*)
  type t = Vector.t IntMap.t ref * (string, Vector.t) Hashtbl.t * arc list ref * (int -> int) ref
  
  let empty () = (ref IntMap.empty, Hashtbl.create 10, ref [], ref (fun (x : int) -> 0))
 
  let add_state (ss,_,_,_) (s_id, sp) = ss := IntMap.add s_id sp (!ss)
  let add_trans (_,ts,_,_) (tname, tpos) = Hashtbl.add ts tname tpos 
  let add_arc        (_,_,arcs,_) arc = arcs := arc::!arcs

  let set_state_fun (_,_,_,f) g = f := g
  let set_state     pet ss' = List.iter (add_state pet) ss'

  let get_states (i,_,_,_)  = !i
  let get_trans  (_,ts,_,_) = ts
  let get_state_for_proc (_,_,_,f) p = !f p
  let get_arcs (_,_,a,_) = !a

end

let petrinstance = ref (Petri.empty ())
let set_petri p  = petrinstance := p
let get_petri () = !petrinstance

let pre_init () = 
    let ws = string_of_int window_size in
    open_graph (" "^ws^"x"^ws);
    auto_synchronize false

let draw_for_state () =
  clear_graph ();

  let sttable = Petri.get_states (get_petri ()) in
  let trtable = Petri.get_trans  (get_petri ()) in

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
    | Petri.In(st,tr) -> 
        let (f,s) = (IntMap.find st sttable, Hashtbl.find trtable tr)         in
        let diff = Vector.setsize state_size (Vector.sub s f)                 in
        (Vector.add diff f),s
    | Petri.Out(tr,st) -> 
        let (f,s) = (Hashtbl.find trtable tr, IntMap.find st sttable)         in
        let diff = Vector.setsize state_size (Vector.sub f s)                 in
        f,(Vector.add diff s)
    in
    draw_arrow fst scnd;
  in
  List.iter draw_arc (Petri.get_arcs (get_petri ())); 


  let draw_state state_id ({x; y} : Vector.t) = 
    set_color black;
    draw_circle x y state_size;
    let proc_in_state = ref [] in
    for i=0 to (Utils.get_nb_proc ()-1) do
      let ps = Petri.get_state_for_proc (get_petri ()) i in
      if ps = state_id then proc_in_state := i::(!proc_in_state)
    done;

    let nb_proc = List.length (!proc_in_state) in
    if nb_proc > 0 then
      (
        let procs =
          try
            let ((_, proc), _) = Traces.get (Simulator.full_trace) in
            proc
          with Failure(_) -> []
        in
        let row_size = int_of_float (Float.ceil (Float.sqrt (float_of_int nb_proc))) in
        let psize = (proc_perc * state_size) / (row_size * 100) in
        let rpsize = (psize * proc_space_perc) / 100 in
        let cen = ((row_size-1) * psize) / 4 in
        let xtopleft = x - cen in 
        let ytopleft = y - cen in
        let draw_proc i p =
          let xingrid = i mod row_size in
          let yingrid = i / row_size in
          let rx = xtopleft + (xingrid*psize) in
          let ry = ytopleft + (yingrid*psize) in
          let col = if List.mem p procs then red else black in
          set_color col;
          fill_circle rx ry rpsize;
        in
        List.iteri draw_proc (!proc_in_state);
      )

  in
  IntMap.iter draw_state sttable;

  let ts = trans_size / 2 in
  let draw_trans trans_name ({x;y} : Vector.t) =
    let col =
      try
        let ((t_name, _), _) = Traces.get (Simulator.full_trace) in
        if t_name = trans_name then red else black
      with Failure(_) -> (black)
    in
    set_color col;
    fill_rect (x-ts) (y-ts) trans_size trans_size
  in
  
  Hashtbl.iter draw_trans trtable;
  set_color black;

  synchronize ()
