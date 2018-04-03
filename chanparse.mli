
val fix_recv_assign :
  Variable.t option -> 'a * Ptree.pglob_update -> 'a * Ptree.pglob_update

val fix_recv_upd :
  Variable.t option -> Ptree.pupdate -> Ptree.pupdate

val fix_recv_send :
  Variable.t option ->
  Variable.t * 'a * 'b * Ptree.term ->
  Variable.t * 'a * 'b * Ptree.term

val fix_recv_expr :
  Variable.t option -> Ptree.formula -> Ptree.formula

val forbid_recv :
  Ptree.formula -> unit
