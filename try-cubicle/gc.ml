
type control = {
  mutable minor_heap_size : int;
  mutable major_heap_increment : int;
  mutable space_overhead : int;
  mutable verbose : int;
  mutable max_overhead : int;
  mutable stack_limit : int;
}

let gc = {
  minor_heap_size = 0;
  major_heap_increment = 0;
  space_overhead = 0;
  verbose = 0;
  max_overhead = 0;
  stack_limit = 0;
}

let get () = gc
let set gc = ()
let minor () = ()
let major () = ()
let major_slice _ = 0
let full_major () = ()
let compact () = ()
