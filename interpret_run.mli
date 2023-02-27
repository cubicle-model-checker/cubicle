val run : Interpret_types.global ->
Ast.transition_info Interpret_types.Trans.t ->
Hstring.t list ->
Types.SAtom.t list ->
(int * Hstring.t * Variable.t list * int * int)
Interpret_types.PersistentQueue.t -> Ast.transition_info list -> unit
