open Unix

let u = ref 0.0

let init () = u:=(times()).tms_utime

let get () = (times()).tms_utime -. !u
