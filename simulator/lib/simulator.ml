open Utils
open Model
open Maps

let full_trace = Traces.empty ()

let callbacks = ref ((fun () -> ()), (fun () -> ()), (fun () -> ()))
let set_callbacks nc = callbacks := nc
let pre_init_callback () = 
  let (pic, _,_) = (!callbacks) in
  pic ()

let post_init_callback () = 
  let (_, poc, _) = !callbacks in
  poc ()

let on_model_change_callback () =
  let (_,_,omc) = !callbacks in
  omc ()

(* -- Interaction variables -- *)

(* Lock is similar to req but it is created at runtime and can be used in scene *)
let runtime_lock : (string, (int list -> bool)) Hashtbl.t = Hashtbl.create 10
let is_paused = ref false
let sleep_time = ref 1.
let get_sleep_time () = !sleep_time
let set_sleep_time st = sleep_time := st

(* -- Simulation -- *)

let init () =
  pre_init_callback ();
  Random.init (int_of_float (Sys.time ()));
  let minit = Model.get_init model in
  minit ();
  Traces.add full_trace (("init", []), Utils.get_model_state ());
  post_init_callback ()

let get_possible_action_for_arg arg trans_list trans_map = 
  let sub_gpafa returned name = 
    let (req, ac) = Hashtbl.find trans_map name in
    let lock      = try Hashtbl.find runtime_lock name with Not_found -> (fun _ -> true) in
    if (req arg && lock arg) then ((arg,ac,name)::returned) else returned in
  List.fold_left sub_gpafa [] trans_list

let take_transition tname args = 
  let (trans_map, _) = Model.get_trans model in
  let (req, ac) = Hashtbl.find trans_map tname in
  if req args then
  (
    ac args;
    let ntr = ((tname, args), Utils.get_model_state ()) in
    Traces.add full_trace ntr;
    on_model_change_callback ();
    true
  ) else false

let take_transition_if_possible tname = 
  let (trans_map, trans_table) = Model.get_trans model in
  let arg_number = ref (-1) in 
  Hashtbl.iter (fun k -> fun v -> if List.mem tname v then arg_number := k) trans_table;
  if !arg_number < 0 then false else 
  (
    let args_list = get_args !arg_number in 
    List.exists (fun arg -> take_transition tname arg) args_list 
  )


let step () =
  if not !is_paused then
  (
  let possible_actions = 
    let returned_list = ref [] in 
    let (trans_map, trans_table) = Model.get_trans model in
    let test_transition arg_number trans_list =
      if arg_number > get_nb_proc () then failwith (Format.sprintf "More than %d proc is required for this simulation." (arg_number))
      else
      let arg_list = get_args arg_number in
      List.iter (fun arg -> returned_list := (get_possible_action_for_arg arg trans_list trans_map)@(!returned_list)) arg_list
    in
    Hashtbl.iter test_transition trans_table;
    !returned_list
  in
  if List.length possible_actions > 0 then  
    let (arg, ac, name) = get_random_in_list possible_actions in
    ignore(take_transition name arg);
  )

(* Interaction functions *)

let lock_trans trans_name =
  Hashtbl.add runtime_lock trans_name (fun _ -> false)

let unlock_trans trans_name =
  Hashtbl.remove runtime_lock trans_name

let toggle_pause () = is_paused := not (!is_paused); on_model_change_callback ()

let add_lock trans_name lfun = Hashtbl.add runtime_lock trans_name lfun

let take_step_back () =
  Traces.prev full_trace;
  let (_, ms) = Traces.get full_trace in
  Model.set_state model ms;
  on_model_change_callback ()

let take_step_forward () = 
  let pre_paused = !is_paused in
  is_paused := false;
  step ();
  is_paused := pre_paused;
  on_model_change_callback ()

let reset () = init ()

let get_model_state () =
  let (_, ret) = Traces.get full_trace in ret

let get_last_trace () = Traces.get full_trace

let is_unsafe () = 
  let res = ref false in
  let test_unsafes arg_number unsafe_list =
    if arg_number < get_nb_proc () then 
      (
      let arg_list = get_args arg_number in
      let test_unsafe uns = List.exists (fun arg -> uns arg) arg_list in 
      if (List.exists (fun uns -> test_unsafe uns) unsafe_list) then res := true
    ) 
  in
  Hashtbl.iter test_unsafes (Model.get_unsafe model);
  !res

(* Scene functions *)

(* Need to be carefull with this one *)
let set_var var_name var_val = 
  let mstate = StringMap.add var_name var_val (get_model_state ()) in 
  Traces.add full_trace ((Format.sprintf "Manually set %s " var_name, []), mstate);
  let (_, ms) = Traces.get full_trace in
  Model.set_state model ms;
  on_model_change_callback ()

let get_vuv vuv_name = try StringMap.find vuv_name (get_model_state ()) 
                      with Not_found -> failwith (Format.sprintf "(Simulator) Could'nt get vuv '%s' : Not_found)" vuv_name)

let get_vuv_const vuv_name =
  match get_vuv vuv_name with 
  | Val v -> v 
  | _ -> failwith "(Simulator) Requested vuv is not a val"

let get_vuv_for_proc vuv_name i = 
  match get_vuv vuv_name with 
  | Arr a -> List.nth a i 
  | _ -> failwith "(Simulator) Requested vuv is not an arr"

let get_vuv_for_proc_pair vuv_name i j = 
  match get_vuv vuv_name with 
  | Mat m -> List.nth (List.nth m i) j 
  | _ -> failwith "(Simulator) Requested vuv is not a mat"

let current_step () = Traces.current_step full_trace 
