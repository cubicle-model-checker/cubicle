val eval_arith : Types.term ->
Interpret_types.interpret_value Interpret_types.Env.t ->
Hstring.t -> Interpret_types.conc_value

val check_unsafe : Interpret_types.interpret_value Interpret_types.Env.t * 'a * 'b * 'c ->
('d * Hstring.t list * Types.SAtom.t) list -> unit


val check_comp : Interpret_types.Env.key -> Interpret_types.Env.key -> Interpret_types.interpret_value Interpret_types.Env.t ->
Variable.subst -> Types.op_comp -> bool

val gen_array : Hstring.t -> Variable.t list -> Types.term list

val gen_array_eq_proc : Hstring.t -> Variable.t list -> (Types.term * Variable.t list) list

val gen_array_combs : Hstring.t -> Variable.t list -> Variable.t list list

  

val check_reqs : Types.SAtom.t ->
Interpret_types.interpret_value Interpret_types.Env.t ->
Variable.subst -> Hstring.t -> unit


val apply_transition : Variable.t list ->
Interpret_types.Trans.key ->
Ast.transition_info Interpret_types.Trans.t ->
Interpret_types.interpret_value Interpret_types.Env.t *
Types.Term.t Interpret_types.PersistentQueue.t Interpret_types.LockQueues.t *
Types.Term.t list Interpret_types.Conditions.t *
Interpret_types.Env.key list Interpret_types.Semaphores.t ->
Interpret_types.interpret_value Interpret_types.Env.t *
Types.Term.t Interpret_types.PersistentQueue.t Interpret_types.LockQueues.t *
Types.Term.t list Interpret_types.Conditions.t *
Interpret_types.Env.key list Interpret_types.Semaphores.t


val all_possible_transitions : Interpret_types.interpret_value Interpret_types.Env.t * 'a * 'b * 'c ->
Ast.transition_info Interpret_types.Trans.t ->
  Hstring.t list -> bool -> (Ast.transition_info * Variable.t list) list

val possible_for_proc : Interpret_types.interpret_value Interpret_types.Env.t * 'a * 'b * 'c ->
Ast.transition_info Interpret_types.Trans.t ->
Hstring.t list ->
Hstring.t ->
(Ast.transition_info * Variable.t list) list *
(Ast.transition_info * Variable.t list) list


val check_duplicates : 'a list -> unit

val explain : Variable.t list ->
Interpret_types.Trans.key ->
Ast.transition_info Interpret_types.Trans.t ->
Interpret_types.interpret_value Interpret_types.Env.t * 'a * 'b * 'c -> unit
