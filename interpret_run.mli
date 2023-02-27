val run : Interpret_types.interpret_value Interpret_types.Env.t *
Types.Term.t Interpret_types.PersistentQueue.t Interpret_types.LockQueues.t *
Types.Term.t list Interpret_types.Conditions.t *
Interpret_types.Env.key list Interpret_types.Semaphores.t ->
Ast.transition_info Interpret_types.Trans.t ->
Hstring.t list ->
Types.SAtom.t list ->
(int * Hstring.t * Variable.t list * int * int)
Interpret_types.PersistentQueue.t -> Ast.transition_info list -> unit
