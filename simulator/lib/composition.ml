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

let expand_grid 
  (center : Vector.t)
  (cell_height : int)
  (cell_width  : int)
  (total_cell_count : int)
  (cell_number : int) 
  : Vector.t = 
  let total_cell_count_side = int_of_float (Float.ceil (Float.sqrt (float_of_int total_cell_count))) in
  let total_width = total_cell_count_side * cell_width   in 
  let total_height = total_cell_count_side * cell_height in
  let xingrid = cell_number mod total_cell_count_side in
  let yingrid = cell_number / total_cell_count_side in
  let offset = Vector.sub center { x = total_width / 2; y = total_height / 2 } in 
  {
    x = center.x + offset.x + cell_width * xingrid;
    y = center.y + offset.y + cell_height * yingrid;
  }

let fit_row 
  (center : Vector.t)
  (total_width : int)
  (total_cell_count : int)
  (cell_number : int)
  : Vector.t = 
  let cell_width = total_width / total_cell_count in 
  let offset = Vector.sub center { x = total_width / 2; y = 0 } in
  {
    x = center.x + offset.x + cell_width * cell_number;
    y = center.y + offset.y;
  }

let fit_col
  (center : Vector.t)
  (total_height : int)
  (total_cell_count : int)
  (cell_number : int)
  : Vector.t = 
  let cell_height = total_height / total_cell_count in 
  let offset = Vector.sub center { x = total_height / 2; y = 0 } in
  {
    x = center.x + offset.x;
    y = center.y + offset.y + cell_height * cell_number;
  }
