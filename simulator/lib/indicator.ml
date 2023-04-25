type t = 
  {
    name : string;
    f    : unit -> bool;
    pos  : Vector.t;
    size : int;
    color_off : Color.t;
    color_on  : Color.t;
  }
