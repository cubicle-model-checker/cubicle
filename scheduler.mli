type error = MustBeSingleNum
exception ETrue
exception EFalse
exception Inversion
exception ConstrRep
exception Error of error
val init_proc : bool
val error : error -> 'a
type value =
    Var of Hstring.t
  | Numb of Num.num
  | Hstr of Hstring.t
  | Proc of int
val compare_value : value -> value -> int
val vequal : value -> value -> bool
type stype = RGlob of Hstring.t | RArr of (Hstring.t * int)
type ty = A | N | O
val fproc : value ref
val list_threads : int list
val trans_list :
  (Hstring.t * (unit -> bool) list * (unit -> bool) list list list *
   ((unit -> unit) list *
    ((unit -> bool) list * (unit -> unit)) list list list))
  list ref
module type OrderedType = sig type t val compare : t -> t -> int end
module OrderedValue :
  sig type t = value val compare : value -> value -> int end
module type DA =
  sig
    type elt
    type t
    val init : int -> int -> elt -> t
    val minit : int -> int -> (elt * int) list -> elt -> t
    val get : t -> int list -> elt
    val set : t -> int list -> elt -> unit
    val print : t -> (Format.formatter -> elt -> unit) -> unit
    val copy : t -> t
    val dim : t -> int
    val dcompare : t -> t -> int
    val equal : t -> t -> bool
  end
module DimArray :
  functor (Elt : OrderedType) ->
    sig
      type elt = Elt.t
      type t
      val init : int -> int -> elt -> t
      val minit : int -> int -> (elt * int) list -> elt -> t
      val get : t -> int list -> elt
      val set : t -> int list -> elt -> unit
      val print : t -> (Format.formatter -> elt -> unit) -> unit
      val copy : t -> t
      val dim : t -> int
      val dcompare : t -> t -> int
      val equal : t -> t -> bool
    end
module type St =
  sig
    type elt
    type da
    type t = {
      globs : (Hstring.t, elt) Hashtbl.t;
      arrs : (Hstring.t, da) Hashtbl.t;
    }
    val init : unit -> t
    val giter :
      (Hstring.t -> elt -> unit) -> (Hstring.t, elt) Hashtbl.t -> unit
    val aiter :
      (Hstring.t -> da -> unit) -> (Hstring.t, da) Hashtbl.t -> unit
    val ecompare : t -> t -> int
    val equal : t -> t -> bool
    val get_v : t -> Hstring.t -> elt
    val get_a : t -> Hstring.t -> da
    val get_e : t -> Hstring.t -> int list -> elt
    val set_v : t -> Hstring.t -> elt -> unit
    val set_a : t -> Hstring.t -> da -> unit
    val set_e : t -> Hstring.t -> int list -> elt -> unit
    val copy : t -> t
  end
module State :
  functor (Elt : OrderedType) ->
    functor
      (A : sig
             type elt = Elt.t
             type t
             val init : int -> int -> elt -> t
             val minit : int -> int -> (elt * int) list -> elt -> t
             val get : t -> int list -> elt
             val set : t -> int list -> elt -> unit
             val print : t -> (Format.formatter -> elt -> unit) -> unit
             val copy : t -> t
             val dim : t -> int
             val dcompare : t -> t -> int
             val equal : t -> t -> bool
           end) ->
      sig
        type elt = Elt.t
        type da = A.t
        type t = {
          globs : (Hstring.t, elt) Hashtbl.t;
          arrs : (Hstring.t, da) Hashtbl.t;
        }
        val init : unit -> t
        val giter :
          (Hstring.t -> elt -> unit) -> (Hstring.t, elt) Hashtbl.t -> unit
        val aiter :
          (Hstring.t -> da -> unit) -> (Hstring.t, da) Hashtbl.t -> unit
        val ecompare : t -> t -> int
        val equal : t -> t -> bool
        val get_v : t -> Hstring.t -> elt
        val get_a : t -> Hstring.t -> da
        val get_e : t -> Hstring.t -> int list -> elt
        val set_v : t -> Hstring.t -> elt -> unit
        val set_a : t -> Hstring.t -> da -> unit
        val set_e : t -> Hstring.t -> int list -> elt -> unit
        val copy : t -> t
      end
module type Sys =
  sig
    type elt
    type s
    type da
    module SSet :
      sig
        type elt = Hstring.t * s
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
    type set = SSet.t
    type t = { syst : set; init : set; read_st : s; write_st : s; }
    val init : unit -> t
    val get_v : t -> Hstring.t -> elt
    val get_a : t -> Hstring.t -> da
    val get_e : t -> Hstring.t -> int list -> elt
    val set_v : t -> Hstring.t -> elt -> unit
    val set_a : t -> Hstring.t -> da -> unit
    val set_e : t -> Hstring.t -> int list -> elt -> unit
    val exists : (s -> bool) -> t -> bool
    val update_init : t -> Hstring.t * s -> t
    val get_init : t -> set
    val new_init : Hstring.t -> t -> s -> t
    val update_s : Hstring.t -> t -> t
  end
module MSystem :
  functor (Elt : OrderedType) ->
    functor
      (A : sig
             type elt = Elt.t
             type t
             val init : int -> int -> elt -> t
             val minit : int -> int -> (elt * int) list -> elt -> t
             val get : t -> int list -> elt
             val set : t -> int list -> elt -> unit
             val print : t -> (Format.formatter -> elt -> unit) -> unit
             val copy : t -> t
             val dim : t -> int
             val dcompare : t -> t -> int
             val equal : t -> t -> bool
           end) ->
      functor
        (E : sig
               type elt = Elt.t
               type da = A.t
               type t = {
                 globs : (Hstring.t, elt) Hashtbl.t;
                 arrs : (Hstring.t, da) Hashtbl.t;
               }
               val init : unit -> t
               val giter :
                 (Hstring.t -> elt -> unit) ->
                 (Hstring.t, elt) Hashtbl.t -> unit
               val aiter :
                 (Hstring.t -> da -> unit) ->
                 (Hstring.t, da) Hashtbl.t -> unit
               val ecompare : t -> t -> int
               val equal : t -> t -> bool
               val get_v : t -> Hstring.t -> elt
               val get_a : t -> Hstring.t -> da
               val get_e : t -> Hstring.t -> int list -> elt
               val set_v : t -> Hstring.t -> elt -> unit
               val set_a : t -> Hstring.t -> da -> unit
               val set_e : t -> Hstring.t -> int list -> elt -> unit
               val copy : t -> t
             end) ->
        sig
          type elt = Elt.t
          type s = E.t
          type da = A.t
          module SSet :
            sig
              type elt = Hstring.t * s
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
          type set = SSet.t
          type t = { syst : set; init : set; read_st : s; write_st : s; }
          val init : unit -> t
          val get_v : t -> Hstring.t -> elt
          val get_a : t -> Hstring.t -> da
          val get_e : t -> Hstring.t -> int list -> elt
          val set_v : t -> Hstring.t -> elt -> unit
          val set_a : t -> Hstring.t -> da -> unit
          val set_e : t -> Hstring.t -> int list -> elt -> unit
          val exists : (s -> bool) -> t -> bool
          val update_init : t -> Hstring.t * s -> t
          val get_init : t -> set
          val new_init : Hstring.t -> t -> s -> t
          val update_s : Hstring.t -> t -> t
        end
module Array :
  sig
    type elt = OrderedValue.t
    type t = DimArray(OrderedValue).t
    val init : int -> int -> elt -> t
    val minit : int -> int -> (elt * int) list -> elt -> t
    val get : t -> int list -> elt
    val set : t -> int list -> elt -> unit
    val print : t -> (Format.formatter -> elt -> unit) -> unit
    val copy : t -> t
    val dim : t -> int
    val dcompare : t -> t -> int
    val equal : t -> t -> bool
  end
module Etat :
  sig
    type elt = OrderedValue.t
    type da = Array.t
    type t =
      State(OrderedValue)(Array).t = {
      globs : (Hstring.t, elt) Hashtbl.t;
      arrs : (Hstring.t, da) Hashtbl.t;
    }
    val init : unit -> t
    val giter :
      (Hstring.t -> elt -> unit) -> (Hstring.t, elt) Hashtbl.t -> unit
    val aiter :
      (Hstring.t -> da -> unit) -> (Hstring.t, da) Hashtbl.t -> unit
    val ecompare : t -> t -> int
    val equal : t -> t -> bool
    val get_v : t -> Hstring.t -> elt
    val get_a : t -> Hstring.t -> da
    val get_e : t -> Hstring.t -> int list -> elt
    val set_v : t -> Hstring.t -> elt -> unit
    val set_a : t -> Hstring.t -> da -> unit
    val set_e : t -> Hstring.t -> int list -> elt -> unit
    val copy : t -> t
  end
module Syst :
  sig
    type elt = OrderedValue.t
    type s = Etat.t
    type da = Array.t
    module SSet :
      sig
        type elt = Hstring.t * s
        type t = MSystem(OrderedValue)(Array)(Etat).SSet.t
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
    type set = SSet.t
    type t =
      MSystem(OrderedValue)(Array)(Etat).t = {
      syst : set;
      init : set;
      read_st : s;
      write_st : s;
    }
    val init : unit -> t
    val get_v : t -> Hstring.t -> elt
    val get_a : t -> Hstring.t -> da
    val get_e : t -> Hstring.t -> int list -> elt
    val set_v : t -> Hstring.t -> elt -> unit
    val set_a : t -> Hstring.t -> da -> unit
    val set_e : t -> Hstring.t -> int list -> elt -> unit
    val exists : (s -> bool) -> t -> bool
    val update_init : t -> Hstring.t * s -> t
    val get_init : t -> set
    val new_init : Hstring.t -> t -> s -> t
    val update_s : Hstring.t -> t -> t
  end
val system : Syst.t ref
val htbl_types : (Hstring.t, value list) Hashtbl.t
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
module TIS :
  sig
    type elt = Hstring.t * TS.t * TI.t
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
val htbl_abstypes : (Hstring.t, Hstring.t * TI.t) Hashtbl.t
val ec : (Hstring.t, value * stype) Hashtbl.t
val dc : (Hstring.t, ty * TS.t * TI.t * int) Hashtbl.t
val inits : (int, TIS.t) Hashtbl.t
val init_list :
  (Hstring.t * stype * TS.t * (Hstring.t * stype) list) list ref
val value_c : int Ast.MConst.t -> Num.num
val find_op : Ast.op_comp -> 'a -> 'a -> bool
val find_nop : Ast.op_comp -> Num.num -> Num.num -> bool
val default_type : Hstring.t -> value
val inter : 'a list -> 'a list -> 'a list
val rep_name : Hstring.t -> Hstring.t
val hst_var : value -> Hstring.t
val ec_replace : value -> value -> unit
val abst_replace : Hstring.t -> Hstring.t -> TI.t -> unit
val get_cvalue : Ast.term -> value
val get_value : (Hstring.t * int) list -> Ast.term -> Syst.elt
val v_equal : value -> value -> bool
val type_st : stype -> Hstring.t
val print_value : 'a -> value -> unit
val print_ce_diffs : unit -> unit
val print_abst : unit -> unit
val print_types : unit -> unit
val print_inits : unit -> unit
val print_init_list : unit -> unit
val print_system : Hstring.t * Etat.t -> unit
val print_init : unit -> unit
val print_procinit : unit -> unit
val print_procninit : unit -> unit
val init_types :
  (Hstring.t * Hstring.t list) list ->
  (Hstring.t * Hstring.t) list -> (Hstring.t * ('a * Hstring.t)) list -> unit
val init_globals : (Hstring.t * Hstring.t) list -> unit
val init_arrays : (Hstring.t * ('a list * Hstring.t)) list -> unit
val init_htbls : 'a * Ast.SAtom.t list -> unit
val upd_options : unit -> unit
val upd_init_list : Hstring.t -> TS.t -> unit
val upd_inits : unit -> unit
val graph_coloring : unit -> unit
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
val get_value_st : (Hstring.t * int) list -> Etat.t -> Ast.term -> Etat.elt
val contains : (Hstring.t * int) list -> Ast.SAtom.t -> 'a -> bool
val filter : Ast.t_system list -> Ast.t_system option
val scheduler : Ast.system -> unit
val dummy_system : Ast.system
val current_system : Ast.system ref
val register_system : Ast.system -> unit
val run : unit -> unit
