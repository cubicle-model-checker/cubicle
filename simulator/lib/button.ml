type t = {
  name: string;
  f: unit->bool;
  pos: Vector.t;
  size: int;
  color_success : Color.t;
  color_failure : Color.t;
  color_off     : Color.t;
  color_hover   : Color.t;
}
