
(* val fix_thr :
 *   Variable.t option -> Hstring.t -> Hstring.t -> Variable.t list -> Types.term *)

val fix_rd_upd :
  Variable.t option -> Ptree.pupdate -> Ptree.pupdate

val fix_rd_assign :
  Variable.t option -> 'a * Ptree.pglob_update -> 'a * Ptree.pglob_update

val fix_rd_write :
  Variable.t option ->
  Variable.t option * 'a * 'b * Ptree.pglob_update ->
  Variable.t * 'a * 'b * Ptree.pglob_update

val fix_rd_expr :
  Variable.t option -> Ptree.formula -> Ptree.formula

val fix_rd_init :
  Ptree.formula -> Ptree.formula
