val root : Ed_graph.G.vertex option ref

val reset_table_and_canvas : unit -> unit

val open_graph : string -> unit

val graph_trace : string Queue.t

val refresh_display : unit -> unit

val refresh_draw : unit -> unit

val model_reset : unit -> unit 
