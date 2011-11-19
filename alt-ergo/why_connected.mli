open Why_annoted


val toggle_prune_nodep : 'a annoted -> GText.tag -> unit

val connect : env -> unit

val clear_used_lemmas_tags : env -> unit

val show_used_lemmas : env -> Explanation.t -> unit

val prune_unused : env -> unit
