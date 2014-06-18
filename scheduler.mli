type error = MustBeSingleNum
exception ETrue
exception EFalse
exception ConstrRep
exception TEnd of int
exception Error of error
val init_proc : bool
val error : error -> 'a
val compare_value : Options.value -> Options.value -> int
val vequal : Options.value -> Options.value -> bool
type stype = RGlob of Hstring.t | RArr of (Hstring.t * int)
val hst : stype -> Hstring.t
type ty = A | N | O
val list_threads : int list
val trans_list :
  (Hstring.t * Hstring.t list * int * (unit -> bool) list *
   (unit -> bool) list list list *
   ((unit -> unit) list *
    ((unit -> bool) list * (unit -> unit)) list list list))
  list ref
module type OrderedType = sig type t val compare : t -> t -> int end
module OrderedValue :
  sig
    type t = Options.value
    val compare : Options.value -> Options.value -> int
  end
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
    type key = Etat.t
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val max_binding : 'a t -> key * 'a
    val choose : 'a t -> key * 'a
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  end
val system : (Hstring.t * Hstring.t list) list Syst.t ref
val sinits : (Hstring.t * Hstring.t list) list Syst.t ref
val read_st : Etat.t ref
val write_st : Etat.t ref
val htbl_types : (Hstring.t, Options.value list) Hashtbl.t
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
    type elt = Options.value
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
val ec : (Hstring.t, Etat.elt * stype) Hashtbl.t
val dc : (Hstring.t, ty * TS.t * TI.t * int) Hashtbl.t
val inits : (int, TIS.t) Hashtbl.t
val init_list :
  (Hstring.t * stype * TS.t * (Hstring.t * stype) list) list ref
val ntValues : (Hstring.t, Options.value list) Hashtbl.t
val print_time : Format.formatter -> float -> unit
val value_c : int Ast.MConst.t -> Num.num
val find_op : Ast.op_comp -> 'a -> 'a -> bool
val find_nop : Ast.op_comp -> Num.num -> Num.num -> bool
val default_type : Hstring.t -> Options.value
val inter : 'a list -> 'a list -> 'a list
val rep_name : Hstring.t -> Hstring.t
val hst_var : Options.value -> Hstring.t
val ec_replace : TS.elt -> TS.elt -> unit
val abst_replace : Hstring.t -> Hstring.t -> TI.t -> unit
val get_cvalue : Ast.term -> Options.value
val get_value : (Hstring.t * int) list -> Ast.term -> Etat.elt
val v_equal : Options.value -> Options.value -> bool
val type_st : stype -> Hstring.t
val print_value : 'a -> Options.value -> unit
val print_ce : unit -> unit
val print_diffs : unit -> unit
val print_ntv : unit -> unit
val print_abst : unit -> unit
val print_types : unit -> unit
val print_inits : unit -> unit
val print_init_list : unit -> unit
val print_state : Etat.t -> unit
val print_system : Etat.t -> (Hstring.t * Hstring.t list) list -> unit
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
val fill_ntv : unit -> unit
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
module TSet :
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
val pTrans : TSet.t ref
val tTrans : TSet.t ref
val ntTrans : TSet.t ref
val iTrans : TSet.t ref
val valid_trans_list :
  unit ->
  ((Hstring.t * Hstring.t list) *
   ((unit -> unit) list *
    ((unit -> bool) list * (unit -> unit)) list list list))
  list
val update_system_alea :
  Etat.t -> (Hstring.t * Hstring.t list) list -> int -> unit
val compare : (TSet.elt * 'a) * 'b -> (TSet.elt * 'c) * 'd -> int
val find_and_exec_gt :
  ('a *
   ((unit -> unit) list *
    ((unit -> bool) list * (unit -> unit)) list list list))
  list ->
  'a *
  ('a *
   ((unit -> unit) list *
    ((unit -> bool) list * (unit -> unit)) list list list))
  list
val update_system_dfs :
  int ->
  Etat.t option ->
  (Etat.t *
   ((Hstring.t * Hstring.t list) *
    ((unit -> unit) list *
     ((unit -> bool) list * (unit -> unit)) list list list))
   list)
  list -> unit
val update_system_bfs : int -> Syst.key -> 'a -> unit
val get_value_st : (Hstring.t * int) list -> Etat.t -> Ast.term -> Etat.elt
val contains : (Hstring.t * int) list -> Ast.SAtom.t -> 'a -> bool
val filter : Ast.t_system list -> Ast.t_system option
val hist_cand : Ast.t_system -> Syst.key * (Hstring.t * Hstring.t list) list
val scheduler : 'a -> unit
val dummy_system : Ast.system
val current_system : Ast.system ref
val register_system : Ast.system -> unit
val init_sched : unit -> unit
val run : unit -> unit
