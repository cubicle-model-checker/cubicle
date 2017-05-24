
open Weakmem
open Weakevent
open Types
       
val satisfy_reads : SAtom.t -> SAtom.t list
					   
val satisfy_unsatisfied_reads : SAtom.t -> SAtom.t

val instantiate_init_evts : SAtom.t -> SAtom.t

val remove_reads : SAtom.t -> SAtom.t
