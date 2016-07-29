val comments : bool ref

val open_c : string ref

val close_c : string ref 

val print_psystem : Ptree.psystem -> Format.formatter -> unit

val psystem_to_string : Ptree.psystem -> string

val psystem_to_string_nocomments : Ptree.psystem -> string
