open Ast
open Types 
open Atom

(* Global variables used for compiling *)
val tmp_file_name : string (* File to write compiled program to *)
val out_file : out_channel 
val var_prefix : string  
val updated_prefix : string
val pfile : ('a, out_channel, unit) format -> 'a (* Print to file *)

(* Helpful functions *)
val get_var_name : Hstring.t -> string 
val get_updated_name : Hstring.t -> string 
val get_constr_name : Hstring.t -> string 
val get_value_for_type : Hstring.t -> (Hstring.t, Hstring.t list) Hashtbl.t -> string
val get_random_for_type : Hstring.t -> (Hstring.t, Hstring.t list) Hashtbl.t -> string (* Returns a string that correspond to an ocaml expression for getting a random value for a certain type *)

val mconst_is_float : 'a Types.MConst.t -> (Hstring.t * 'b) Hstring.HMap.t -> bool 
val deplier_var_list : Hstring.t list -> string 

val mult_string : string -> int -> string

val deplier_var : int -> string

val hstring_list_to_string : Hstring.t list -> string 
val const_to_string : Types.const -> string
val mconst_to_string : int Types.MConst.t -> string
val const_ref_to_string : Types.const -> string 

(* print_* functions write to the out_file *)
val print_const : Types.const -> unit
val print_mconst : int Types.MConst.t -> unit 
val print_mconst_ref : 'a Types.MConst.t -> unit
val print_term : (Hstring.t * 'a) Hstring.HMap.t -> Types.term -> unit 

val get_var_type : Hstring.HMap.key -> ('a * 'b) Hstring.HMap.t -> 'a (* Take a var as an argument and return it's type. *)
val get_var_dim : Hstring.HMap.key -> ('a * int) Hstring.HMap.t -> int (* Take a var as an arguments and return it's dim. Dimension correspond to -1 if var is as constr *)

module IntMap : Map.S with type key = Int.t 
