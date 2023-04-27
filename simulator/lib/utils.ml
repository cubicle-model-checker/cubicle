open Format
open Maps

(* Getters and setters *)
let scene         = ref Scene.empty
let set_scene s   = scene := s
let get_scene ()  = !scene

let model        = ref Model.empty
let set_model m  = model := m
let get_model () = !model
let get_model_state () = Model.get_state (!model)

let nb_proc         = ref 0 
let get_nb_proc ()  = !nb_proc
let set_nb_proc nbp = nb_proc := nbp 

(* Debug functions *)

let dumper () = 
  let mstate = Model.get_state (!model) in
  printf "-------- BEGIN DUMP --------\n";
  let print_var val_name val_value =
    printf "%s : " val_name;
    let pval v = printf "%s " (Model.vuv_to_string v) in
    let parr a = 
      printf "[ ";
      List.iter pval a; 
      printf "]"
    in
    let pmat m = 
      printf "[ ";
      List.iter parr m;
      printf "]"
    in
    begin match val_value with
      | Traces.Val(v) -> pval v
      | Traces.Arr(a) -> parr a
      | Traces.Mat(m) -> pmat m
    end;
    printf "\n"
  in
  StringMap.iter print_var mstate;
  printf "-------- END DUMP --------\n%!"

let print_list_int l =
  Format.printf "[ %s ]\n\n" (String.concat " " (List.map string_of_int l))

(* Simulation functions *)

let get_random_in_list l =
  List.nth l (Random.int (List.length l))

let get_random_proc () =
  Random.int (get_nb_proc ())

(* Renvoie toutes les combinaisons possible de n éléments parmi nb_proc(), ne contenant pas deux fois le même élément *)
let computed_args = Hashtbl.create 124 

let rec get_args n = 
  try Hashtbl.find computed_args n with Not_found ->
  if n <= 0 then [[]] else 
  let prev = (get_args (n-1)) in 
  let sub l = 
    let res = ref [] in 
    for i = 0 to get_nb_proc () - 1 do 
      res := (i::l) :: !res
    done;
    !res 
  in
  let res = List.map (fun l -> sub l) prev in
  let res_flat = List.flatten res in 
  Hashtbl.add computed_args n res_flat; 
  res_flat

let forall_other f i = 
  let rec forall_sub n =
    if not (List.exists (fun v -> v = n) i) && not (f n) then false else if n == ((get_nb_proc ()) - 1) then true else forall_sub (n+1) in
  forall_sub 0

let forall f = forall_other f []
