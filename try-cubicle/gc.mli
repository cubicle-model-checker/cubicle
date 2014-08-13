
type control = {
  mutable minor_heap_size : int;
  mutable major_heap_increment : int;
  mutable space_overhead : int;
  mutable verbose : int;
  mutable max_overhead : int;
  mutable stack_limit : int;
}

val get : unit -> control
val set : control -> unit
val minor : unit -> unit
val major_slice : int -> int
val major : unit -> unit
val full_major : unit -> unit
val compact : unit -> unit
