open Graphics

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
let trans_size  = 50

(* Petri Settings *)
module Petri : sig
  type arc = 
    | Out of string * int     (* From transition to state *)
    | In  of int    * string  (* From state to transition *)
  
  type pos = { x : int; y : int }
  type t

  val empty               : unit -> t
  val add_state           : t -> pos -> unit
  val add_trans           : t -> (string*pos) -> unit
  val add_arc             : t -> arc -> unit
  val set_state_fun       : t -> (int -> int) -> unit
  val set_state           : t -> pos list -> unit

  val  get_states         : t -> (int, pos) Hashtbl.t
  val  get_trans          : t -> (string,pos) Hashtbl.t
  val  get_state_for_proc : t -> int -> int
  val get_arcs            : t -> arc list
end
=
struct
  
  type arc = 
  | Out of string * int     
  | In  of int    * string
  type pos = { x : int; y : int }
  type t = (int, pos) Hashtbl.t * (string, pos) Hashtbl.t * arc list ref * (int -> int) ref
  
  let empty () = (Hashtbl.create 10, Hashtbl.create 10, ref [], ref (fun (x : int) -> 0))
 
  let add_state (ss,_,_,_) s = Hashtbl.add ss (Hashtbl.length ss) s
  let add_trans (_,ts,_,_) (tname, tpos) = Hashtbl.add ts tname tpos 
  let add_arc        (_,_,arcs,_) arc = arcs := arc::!arcs

  let set_state_fun (_,_,_,f) g = f := g
  let set_state     pet ss' = List.iter (add_state pet) ss'

  let get_states (i,_,_,_)  = i
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

  let draw_state _ ({x; y} : Petri.pos) = draw_circle x y state_size
  in

  Hashtbl.iter draw_state sttable;

  let ts = trans_size / 2 in
  let draw_trans _ ({x;y} : Petri.pos) = 
    draw_rect (x-ts) (y-ts) trans_size trans_size
  in

  Hashtbl.iter draw_trans trtable;

  let draw_arc a = 
    let fst, scnd = match a with
    | Petri.In(st,tr) -> Hashtbl.find sttable st, Hashtbl.find trtable tr
    | Petri.Out(tr,st) -> Hashtbl.find trtable tr, Hashtbl.find sttable st
    in
    (* TODO 
      - Draw arrow
      - Take in account size of different stuffs
    *)

    moveto fst.x fst.y;
    lineto scnd.x scnd.y;
    (* moveto fst, drawline to scnd *) (* Should even be drawing arrow here *)
  in

  List.iter draw_arc (Petri.get_arcs (get_petri ())); 

  synchronize ()
