open Utils

let init () = 
  if get_scene () <> Scene.empty then
    (
      (* Create window and context *)
    )

let update () =
  let s = get_scene () in 
  Scene.update s
