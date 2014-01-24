open Ast
open Why3


let global_system = ref {
  t_globals = [];
  t_arrays = [];
  t_from = [];
  t_init = [],[];
  t_invs = [];
  t_cands = [];
  t_unsafe = [],SAtom.empty;
  t_forward = [];
  t_arru = [||];
  t_alpha = [],[||];
  t_trans = [];
  t_deleted = false;
  t_nb = 0;
  t_nb_father = 0;
  t_glob_proc = [];
  t_from_forall= false;
		      }

let info = ref {
  globals = [];
  consts = [];
  arrays = [];
  type_defs = [];
  init = [],[];
  invs = [];
  cands = [];
  unsafe = [];
  forward = [];
  trans = [];
}


type sys_env = 
    {
      mutable s_init : Term.term;
      mutable s_unsafe : Term.term;
      mutable s_trans : (Mlw_expr.expr * Mlw_ty.pvsymbol list) list;
    }

let sys_env = 
  {
    s_init = Term.t_true;
    s_unsafe = Term.t_true;
    s_trans = [];
  }
