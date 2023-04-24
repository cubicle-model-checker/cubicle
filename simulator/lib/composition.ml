let expand_row
  (center : Vector.t) 
  (cell_width : int) 
  (total_cell_count : int) 
  (cell_number : int)   
  : Vector.t =
  let total_width = total_cell_count * cell_width in 
  let offset = Vector.sub center { x = total_width / 2; y = 0 } in
  {
    x = center.x + offset.x + cell_width * cell_number;
    y = center.y + offset.y;
  }
let expand_col 
  (center : Vector.t) 
  (cell_height : int) 
  (total_cell_count : int) 
  (cell_number : int)   
  : Vector.t =
  let total_height = total_cell_count * cell_height in 
  let offset = Vector.sub center { x = 0; y = total_height / 2 } in
  {
    x = center.x + offset.x;
    y = center.y + offset.y + cell_height * cell_number;
  }

let expand_grid () = failwith "TODO"

let fit_row () = failwith "TODO"
let fit_col () = failwith "TODO"
let fil_grid () = failwith "TODO"
