type proc = int
type direction = Up | Down
type event = Button of int
                    
let arr n p =
  let r = ref [] in
  let rec arr_rec n l =
    if n = 0 then r := l :: !r
    else
      for i = 1 to p do
        if not (List.mem i l) then arr_rec (n-1) (i::l)
      done
  in
  arr_rec n [];
  List.map Array.of_list !r
                      
let random_direction () =
  match Random.int 2 with
  | 0 -> Up
  | 1 -> Down
  | _ -> assert false
                    
let nb_procs = 10
             
let curFloor = ref ((Random.int nb_procs) + 1)
let get_curFloor () = !curFloor

let moving = ref (Random.bool ())
let get_moving () = !moving
           
let dir = ref (random_direction())
let get_dir () = !dir
        
let request = Array.init (nb_procs + 1) (fun i -> false)
let get_request n = request.(n)
            
let next = Array.init (nb_procs + 1) (fun i -> i + 1)
let get_next n = next.(n)

let button = Array.init (nb_procs + 1) (fun i -> false)

let send_button n = button.(n) <- true
let erase_button n = button.(n) <- false

let event e =
  match e with
  | Button n -> button.(n) <- true

let erase e =
  match e with
  | Button n -> button.(n) <- false
                   
           
let forall f =
  try
    for i = 1 to nb_procs do
      if not (f i) then raise Exit
    done;
    true
  with Exit -> false
             
let forall_other j f =
  try
    for i = 1 to nb_procs do
      if i <> j then
        if not (f i) then raise Exit
    done;
    true
  with Exit -> false

let equal s x =
  match s with
  | None -> false
  | Some y -> x = y
  
(* 1 *)
let requires_t_request p =
  button.(p.(0)) && p.(0) <> !curFloor && request.(p.(0)) = false

(* 1 *)
let action_t_request p =
  request.(p.(0)) <- true;
  erase (Button p.(0))

(* 0 *)
let requires_t_change_direction_up p = 
  !moving = false && !dir = Down &&
    forall (fun q -> q >= !curFloor || request.(q) = false)

(* 0 *)
let action_t_change_direction_up p =
  dir := Up

(* 0 *)
let requires_t_change_direction_down p = 
  !moving = false && !dir = Up && 
    forall (fun q -> q <= !curFloor || request.(q) = false)

(* 0 *)
let action_t_change_direction_down p = 
    dir := Down

(* 1 *)
let requires_t_start_move_up p = 
  !moving = false && !dir = Up && p.(0) > !curFloor && request.(p.(0)) = true

(* 0 *)
let action_t_start_move_up p = 
  moving := true 

(* 1 *)
let requires_t_start_move_down p = 
  !moving = false && !dir = Down && p.(0) < !curFloor && request.(p.(0)) = true

(* 0 *)
let action_t_start_move_down p =
    moving := true 

(* 2 ? *)
let requires_t_move_up p =
  !moving = true && !dir = Up && p.(0) = !curFloor && request.(p.(0)) = false
  && next.(p.(0)) = p.(1)

(* 0 *)
let action_t_move_up p =
  curFloor := next.(p.(0))

(* 2 *)
let requires_t_move_down p =
  !moving = true && !dir = Down && p.(0) = !curFloor && request.(p.(0)) = false
  && next.(p.(1)) = p.(0)  

(* 0 *)
let action_t_move_down p =
  curFloor := p.(1)

(* 1 *)
let requires_t_stop p =
  !moving = true && p.(0) = !curFloor && request.(p.(0)) = true

(* 1 *)
let action_t_stop p =               
  moving := false;
  request.(p.(0)) <- false
  
let requires =
  [|
    [ requires_t_change_direction_up, action_t_change_direction_up;
      requires_t_change_direction_down, action_t_change_direction_down
    ];
    
    [ requires_t_request, action_t_request;
      requires_t_start_move_up, action_t_start_move_up;
      requires_t_start_move_down, action_t_start_move_down;
      requires_t_stop, action_t_stop
    ];
    
    [ requires_t_move_up, action_t_move_up;
      requires_t_move_down, action_t_move_down
    ];
    []; []; []; []; [];[];[]; []
  |]

let slow = ref 0
          
let step () =
  let cand = ref [] in
  slow := (!slow + 1) mod 10;
  if !slow = 0 then
    begin
      for i = 0 to nb_procs do
        if List.length requires.(i) > 0 then
          let ai = arr i nb_procs in
          List.iter 
            (fun (r,a) ->
              List.iter
                (fun args -> if r args then cand := (a, args) :: !cand) ai )
            requires.(i)
      done;
      if !cand <> [] then 
        let a,args = List.nth !cand (Random.int (List.length !cand)) in
        a args
    end
