val root : Ed_graph.G.V.t option ref

(* val quit : unit -> unit *)

val reset_table_and_canvas : unit -> unit
 
val var_l : (string * (string list * Ed_graph.condition)) list ref

val mode_change : bool ref

val mode_value : bool ref

val init : string -> int -> bool ref -> unit

val scroll_to_transition : (string ->  unit) ref

(* val model_reset : unit -> unit  *)

val path_to :       Ed_graph.G.E.t ->
           (Ed_graph.Var_Map.key * (string list * Ed_graph.condition)) list -> unit

val path_to_loop : (Ed_graph.Var_Map.key * (string list * Ed_graph.condition)) list -> unit(* unit -> unit *)

(* val cpt : int ref *)
