
val root : Ed_graph.G.vertex option ref

(* val quit : unit -> unit *)

val reset_table_and_canvas : unit -> unit
 
val var_l : (string * (string list * Ed_graph.condition)) list ref

(* list ref (\* Var_L.t *\) *)

(* val open_graph : string -> int ->  unit *)

(* val graph_trace : string Queue.t *)

(* val refresh_display : unit -> unit *)

(* val refresh_draw : unit -> unit *)
(* val mode_equals : bool ref *)

val mode_change : bool ref

val mode_value : bool ref

(* val mode_and : bool ref *)

val init : string -> int -> bool ref -> unit

val scroll_to_transition : (string ->  unit) ref
val model_reset : unit -> unit 

val path_to :       Ed_graph.G.E.t ->
           (Ed_graph.Var_Map.key * (string list * Ed_graph.condition)) list -> unit

val path_to_loop : (Ed_graph.Var_Map.key * (string list * Ed_graph.condition)) list -> unit(* unit -> unit *)

(* val cpt : int ref *)
