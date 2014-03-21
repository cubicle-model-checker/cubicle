type error = MustBeSingleNum
exception ETrue
exception EFalse
exception Error of error
val error : error -> 'a
type value = Int of int | Hstr of Hstring.t | Proc of int
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
    val get : 'a dima -> int list -> 'a
    val set : 'a dima -> int list -> 'a -> unit
    val print : 'a dima -> (Format.formatter -> 'a -> unit) -> unit
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
    end
module type Sys =
  sig
    type 'a s
    type 'a da
    type 'a t = { old_s : 'a s; new_s : 'a s; }
    val init : unit -> 'a t
    val get_v : 'a t -> Hstring.t -> 'a
    val get_a : 'a t -> Hstring.t -> 'a da
    val get_e : 'a t -> Hstring.t -> int list -> 'a
    val set_v : 'a t -> Hstring.t -> 'a -> unit
    val set_a : 'a t -> Hstring.t -> 'a da -> unit
    val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
    val update_s : 'a t -> 'a t
  end
module System :
  functor (S : St) ->
    sig
      type 'a s = 'a S.t
      type 'a da = 'a S.da
      type 'a t = { old_s : 'a s; new_s : 'a s; }
      val init : unit -> 'a t
      val get_v : 'a t -> Hstring.t -> 'a
      val get_a : 'a t -> Hstring.t -> 'a da
      val get_e : 'a t -> Hstring.t -> int list -> 'a
      val set_v : 'a t -> Hstring.t -> 'a -> unit
      val set_a : 'a t -> Hstring.t -> 'a da -> unit
      val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
      val update_s : 'a t -> 'a t
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
  end
module Syst :
  sig
    type 'a s = 'a Etat.t
    type 'a da = 'a Etat.da
    type 'a t = 'a System(Etat).t = { old_s : 'a s; new_s : 'a s; }
    val init : unit -> 'a t
    val get_v : 'a t -> Hstring.t -> 'a
    val get_a : 'a t -> Hstring.t -> 'a da
    val get_e : 'a t -> Hstring.t -> int list -> 'a
    val set_v : 'a t -> Hstring.t -> 'a -> unit
    val set_a : 'a t -> Hstring.t -> 'a da -> unit
    val set_e : 'a t -> Hstring.t -> int list -> 'a -> unit
    val update_s : 'a t -> 'a t
  end
val system : value Syst.t ref
val htbl_types : (Hstring.t, value list) Hashtbl.t
val value_c : int Ast.MConst.t -> int
val find_op : Ast.op_comp -> 'a -> 'a -> bool
val default_type : Hstring.t -> value
val inter : 'a list -> 'a list -> 'a list
val get_value : (Hstring.t * int) list -> Ast.term -> value
val print_value : 'a -> value -> unit
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
val init_types : (Hstring.t * Hstring.t list) list -> unit
val init_globals : (Hstring.t * Hstring.t) list -> unit
val init_arrays : (Hstring.t * ('a list * Hstring.t)) list -> unit
val initialization : 'a * Ast.SAtom.t list -> unit
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
  (unit -> unit) list * ((unit -> bool) list * (unit -> unit)) list list list
val print_globals : unit -> unit
val update_system : unit -> unit
val scheduler : Ast.system -> unit
