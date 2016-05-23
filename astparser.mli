exception Found

val buffer_l : int ref
val buffer_c : int ref

val parse_ast : Ast.system -> GSourceView2.source_buffer -> unit

val parse_modify_ast : Ast.system -> GSourceView2.source_buffer -> unit
