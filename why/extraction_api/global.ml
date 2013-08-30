open Ast

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
