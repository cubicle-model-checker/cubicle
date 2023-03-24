val eval_arith : Types.term ->
Interpret_types.interpret_value Interpret_types.Env.t ->
Hstring.t -> Interpret_types.conc_value

val check_unsafe_prover : Interpret_types.global -> ('d * Hstring.t list * Types.SAtom.t) list -> unit

val check_unsafe : Interpret_types.global-> Types.SAtom.t list -> unit


val check_comp : Interpret_types.Env.key -> Interpret_types.Env.key -> Interpret_types.interpret_value Interpret_types.Env.t -> Variable.subst -> Types.op_comp -> bool

val gen_array : Hstring.t -> Variable.t list -> Types.term list

val gen_array_eq_proc : Hstring.t -> Variable.t list -> (Types.term * Variable.t list) list

val gen_array_combs : Hstring.t -> Variable.t list -> Variable.t list list

  
val check_reqs : Types.SAtom.t ->
Interpret_types.interpret_value Interpret_types.Env.t ->
Variable.subst -> Hstring.t -> unit


val apply_transition : Variable.t list ->
Interpret_types.Trans.key ->
Ast.transition_info Interpret_types.Trans.t ->
Interpret_types.global ->
Interpret_types.global


val all_possible_transitions : Interpret_types.global ->
Ast.transition_info Interpret_types.Trans.t ->
  Hstring.t list -> bool -> (Ast.transition_info * Variable.t list) list

val possible_for_proc : Interpret_types.global->
Ast.transition_info Interpret_types.Trans.t ->
Hstring.t list ->
Hstring.t ->
(Ast.transition_info * Variable.t list) list *
(Ast.transition_info * Variable.t list) list


val check_duplicates : 'a list -> unit

val explain : Variable.t list ->
Interpret_types.Trans.key ->
Ast.transition_info Interpret_types.Trans.t ->
Interpret_types.global -> unit


val init_unsafe : Variable.t list ->
('a * Variable.t list * Types.SAtom.t) list -> Types.SAtom.t list

  
val hash_env : Interpret_types.interpret_value Interpret_types.Env.t -> int


val hash_locks : Types.Term.t Interpret_types.PersistentQueue.t Interpret_types.LockQueues.t -> int

val hash_cond : Types.Term.t list Interpret_types.Conditions.t -> int

val hash_sem : Types.Term.t list Interpret_types.Semaphores.t -> int

val hash_full_env : Interpret_types.global -> int
val hash_full_env_loud : Interpret_types.global -> int


val weight_env : Interpret_types.global -> Types.SAtom.t -> Interpret_types.term_map -> int -> int 

  
val all_possible_weighted_transitions :
           Interpret_types.global ->
           Ast.transition_info Interpret_types.Trans.t ->
           Hstring.t list ->
           Interpret_types.global ->
           Ast.transition_info -> bool -> 
  (int * Ast.transition_info * Variable.t list) list

    
val uguard : (Variable.t * Variable.t) list -> Hstring.t list -> Hstring.t list ->
(Variable.t * Types.SAtom.t list) list -> Types.SAtom.t list

val all_arrange : int -> 'a list -> 'a list list
val all_combs_as_pairs : 'a list -> ('a * 'a) list
val create_transition_hash : Ast.transition_info list -> (Hstring.t * Hstring.t, int) Hashtbl.t

val create_detailed_hash: Ast.transition_info list -> Hstring.t list -> (Hstring.t * Hstring.t, int) Hashtbl.t

  
val entropy_env : Interpret_types.global -> Ast.transition_info Interpret_types.Trans.t -> Hstring.t list -> float


val biased_entropy_env : Interpret_types.global ->
Ast.transition_info Interpret_types.Trans.t ->
  Hstring.t list -> (Hstring.t * float) list -> float

val trans_proc_to_hstring : Hstring.t -> Hstring.t list -> Hstring.t
