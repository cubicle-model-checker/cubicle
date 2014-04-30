type error = MustBeSingleNum
exception ETrue
exception EFalse
exception Inversion
exception ConstrRep
exception Error of error
val report : Lexing.position * Lexing.position -> unit
val init_proc : bool
val error : error -> 'a
type value =
    Var of Hstring.t
  | Numb of Num.num
  | Hstr of Hstring.t
  | Proc of int
type stype = RGlob of Hstring.t | RArr of (Hstring.t * int)
type ty = A | N | O
val fproc : value ref
val list_threads : int list
val trans_list :
  (Hstring.t * (unit -> bool) list * (unit -> bool) list list list *
   ((unit -> unit) list *
    ((unit -> bool) list * (unit -> unit)) list list list))
  list ref
module type DA =
  sig
    type 'a t
    type 'a dima
    val init : int -> int -> 'a -> 'a dima
    val minit : int -> int -> ('a * int) list -> 'a -> 'a dima
    val get : 'a dima -> int list -> 'a
    val set : 'a dima -> int list -> 'a -> unit
    val print : 'a dima -> (Format.formatter -> 'a -> unit) -> unit
    val copy : 'a dima -> 'a dima
    val dim : 'a dima -> int
  end
module DimArray : DA
module type St =
  sig
    type 'a da
    type 'a t = {
      globs : (Hstring.t, 'a) Hashtbl.t;
      arrs : (Hstring.t, 'a da) Hashtbl.t;
    }
    val init : unit -> 'a t
    val equal : 'a t -> 'a t -> bool
    val hash : 'a t -> int
    val get_v : 'a t -> Hstring.t -> 'a
    val get_a : 'a t -> Hstring.t -> 'a da
    val get_e : 'a t -> Hstring.t -> int list -> 'a
    val set_v : 'a t -> Hstring.t -> 'a -> unit
    val set_a : 'a t -> Hstring.t -> 'a da -> unit
    val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
    val copy : 'a t -> 'a t
    val clear : 'a t -> unit
  end
module State :
  functor (A : DA) ->
    sig
      type 'a da = 'a A.dima
      type 'a t = {
        globs : (Hstring.t, 'a) Hashtbl.t;
        arrs : (Hstring.t, 'a da) Hashtbl.t;
      }
      val init : unit -> 'a t
      val equal : 'a t -> 'a t -> bool
      val hash : 'a t -> int
      val get_v : 'a t -> Hstring.t -> 'a
      val get_a : 'a t -> Hstring.t -> 'a da
      val get_e : 'a t -> Hstring.t -> int list -> 'a
      val set_v : 'a t -> Hstring.t -> 'a -> unit
      val set_a : 'a t -> Hstring.t -> 'a da -> unit
      val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
      val copy : 'a t -> 'a t
      val clear : 'a t -> unit
    end
module type Sys =
  sig
    type 'a s
    type 'a da
    type 'a set
    type 'a t = {
      syst : 'a set;
      init : 'a set;
      read_st : 'a s;
      write_st : 'a s;
    }
    val init : unit -> 'a t
    val get_v : 'a t -> Hstring.t -> 'a
    val get_a : 'a t -> Hstring.t -> 'a da
    val get_e : 'a t -> Hstring.t -> int list -> 'a
    val set_v : 'a t -> Hstring.t -> 'a -> unit
    val set_a : 'a t -> Hstring.t -> 'a da -> unit
    val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
    val exists : ('a s -> bool) -> 'a set -> bool
    val update_init : 'a t -> Hstring.t * 'a s -> 'a t
    val get_init : 'a t -> 'a set
    val new_init : Hstring.t -> 'a t -> 'a s -> 'a t
    val update_s : Hstring.t -> 'a t -> 'a t
  end
module System :
  functor (S : St) ->
    sig
      type 'a s = 'a S.t
      type 'a da = 'a S.da
      type 'a set = (Hstring.t * 'a S.t) list
      type 'a t = {
        syst : 'a set;
        init : 'a set;
        read_st : 'a s;
        write_st : 'a s;
      }
      val init : unit -> 'a t
      val get_v : 'a t -> Hstring.t -> 'a
      val get_a : 'a t -> Hstring.t -> 'a da
      val get_e : 'a t -> Hstring.t -> int list -> 'a
      val set_v : 'a t -> Hstring.t -> 'a -> unit
      val set_a : 'a t -> Hstring.t -> 'a da -> unit
      val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
      val exists : ('a s -> bool) -> 'a set -> bool
      val update_init : 'a t -> Hstring.t * 'a s -> 'a t
      val get_init : 'a t -> 'a set
      val new_init : Hstring.t -> 'a t -> 'a s -> 'a t
      val update_s : Hstring.t -> 'a t -> 'a t
    end
module Etat :
  sig
    type 'a da = 'a DimArray.dima
    type 'a t =
      'a State(DimArray).t = {
      globs : (Hstring.t, 'a) Hashtbl.t;
      arrs : (Hstring.t, 'a da) Hashtbl.t;
    }
    val init : unit -> 'a t
    val equal : 'a t -> 'a t -> bool
    val hash : 'a t -> int
    val get_v : 'a t -> Hstring.t -> 'a
    val get_a : 'a t -> Hstring.t -> 'a da
    val get_e : 'a t -> Hstring.t -> int list -> 'a
    val set_v : 'a t -> Hstring.t -> 'a -> unit
    val set_a : 'a t -> Hstring.t -> 'a da -> unit
    val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
    val copy : 'a t -> 'a t
    val clear : 'a t -> unit
  end
module Syst :
  sig
    type 'a s = 'a Etat.t
    type 'a da = 'a Etat.da
    type 'a set = (Hstring.t * 'a Etat.t) list
    type 'a t =
      'a System(Etat).t = {
      syst : 'a set;
      init : 'a set;
      read_st : 'a s;
      write_st : 'a s;
    }
    val init : unit -> 'a t
    val get_v : 'a t -> Hstring.t -> 'a
    val get_a : 'a t -> Hstring.t -> 'a da
    val get_e : 'a t -> Hstring.t -> int list -> 'a
    val set_v : 'a t -> Hstring.t -> 'a -> unit
    val set_a : 'a t -> Hstring.t -> 'a da -> unit
    val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
    val exists : ('a s -> bool) -> 'a set -> bool
    val update_init : 'a t -> Hstring.t * 'a s -> 'a t
    val get_init : 'a t -> 'a set
    val new_init : Hstring.t -> 'a t -> 'a s -> 'a t
    val update_s : Hstring.t -> 'a t -> 'a t
  end
val system : value Syst.t ref
val htbl_types : (Hstring.t, value list) Hashtbl.t
val htbl_abstypes : (Hstring.t, unit) Hashtbl.t
val compare_value : value -> value -> int
module TS :
  sig
    type elt = value
    type t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
  end
module TI :
  sig
    type elt = Hstring.t
    type t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
  end
val ec : (Hstring.t, TS.elt * stype) Hashtbl.t
val dc : (Hstring.t, ty * TS.t * TI.t) Hashtbl.t
val inits : (Hstring.t * (stype * TS.t)) list ref
val upd_dc : Hstring.t -> TS.t -> ty -> TI.t -> unit
val groups : (int, TI.t) Hashtbl.t
val graphs : (int, (Hstring.t * (ty * TS.t * TI.t)) list) Hashtbl.t
val value_c : int Ast.MConst.t -> Num.num
val find_op : Ast.op_comp -> 'a -> 'a -> bool
val find_nop : Ast.op_comp -> Num.num -> Num.num -> bool
val default_type : Hstring.t -> value
val inter : 'a list -> 'a list -> 'a list
val rep_name : Hstring.t -> Hstring.t
val hst_var : value -> Hstring.t
val ec_replace : TS.elt -> TS.elt -> unit
val get_cvalue : Ast.term -> value
val get_value : (Hstring.t * int) list -> Ast.term -> value
val v_equal : value -> value -> bool
val print_value : 'a -> value -> unit
val print_ce_diffs : unit -> unit
val print_g : unit -> unit
val print_groups : unit -> unit
val print_inits : unit -> unit
val print_system : Hstring.t * value Etat.t -> unit
val print_init : unit -> unit
val init_types :
  (Hstring.t * Hstring.t list) list ->
  (Hstring.t * Hstring.t) list -> (Hstring.t * ('a * Hstring.t)) list -> unit
val init_globals : (Hstring.t * Hstring.t) list -> unit
val init_arrays : (Hstring.t * ('a list * Hstring.t)) list -> unit
val init_htbls : 'a * Ast.SAtom.t list -> unit
val c : int ref
val update : unit -> unit
val comp_node : 'a * ('b * TS.t * TI.t) -> 'c * ('d * TS.t * TI.t) -> int
val upd_graphs : unit -> unit
val graphs_to_inits : unit -> unit
val ec_to_inits : unit -> unit
val initialization : 'a * Ast.SAtom.t list -> unit
val subst_req : (Hstring.t * int) list -> Ast.Atom.t -> unit -> bool
val subst_ureq :
  (Hstring.t * int) list ->
  int list ->
  (Hstring.t * Ast.SAtom.t list) list -> (unit -> bool) list list list
val substitute_req :
  (Hstring.t * int) list -> Ast.SAtom.t -> (unit -> bool) list
val substitute_updts :
  (Hstring.t * int) list ->
  (Hstring.t * Ast.term) list ->
  Ast.update list ->
  (unit -> unit) list * ((unit -> bool) list * (unit -> unit)) list list list
val init_system : Ast.system -> unit
val init_transitions : Ast.transition list -> unit
val valid_req : (unit -> bool) list -> bool
val valid_ureq : (unit -> bool) list list list -> bool
val valid_upd : ((unit -> bool) list * 'a) list list list -> 'a list list
val valid_trans_list :
  unit ->
  (Hstring.t *
   ((unit -> unit) list *
    ((unit -> bool) list * (unit -> unit)) list list list))
  list
val random_transition :
  unit ->
  Hstring.t *
  ((unit -> unit) list *
   ((unit -> bool) list * (unit -> unit)) list list list)
val update_system : unit -> unit
val get_value_st :
  (Hstring.t * int) list -> value Etat.t -> Ast.term -> value
val contains : (Hstring.t * int) list -> Ast.SAtom.t -> 'a -> bool
val filter : Ast.t_system list -> Ast.t_system option
val scheduler : Ast.system -> unit
val dummy_system : Ast.system
val current_system : Ast.system ref
val register_system : Ast.system -> unit
val run : unit -> unit
