type t = {
  r : int;
  g : int;
  b : int;
}

let to_graphics c = Graphics.rgb c.r c.g c.b

let red   : t = { r=255 ; g=0   ; b=0   }
let green : t = { r=0   ; g=255 ; b=0   }
let blue  : t = { r=0   ; g=0   ; b=255 }
let black : t = { r=0   ; g=0   ; b=0   }
let white : t = { r=255 ; g=255 ; b=255 }
