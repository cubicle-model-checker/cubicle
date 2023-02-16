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

(* Lock is similar to req but it is created at runtime *)
let runtime_lock : (string, (int list -> bool)) Hashtbl.t = Hashtbl.create 10
let is_paused = ref false
let sleep_time = ref 1.
let get_sleep_time () = !sleep_time
let set_sleep_time st = sleep_time := st

(* -- Simulation -- *)

let init () =
  pre_init_callback ();
  Random.init (int_of_float (Unix.time ()));
  let minit = Model.get_init (get_model ()) in
  minit ();
  Traces.add full_trace (("init", []),Utils.get_model_state ());
  post_init_callback ()

let get_possible_action_for_arg arg trans_list trans_map = 
  let sub_gpafa returned name = 
    let (req, ac) = StringMap.find name trans_map in
    let lock      = try Hashtbl.find runtime_lock name with Not_found -> (fun _ -> true) in
    if (req arg && lock arg) then ((arg,ac,name)::returned) else returned in
  List.fold_left sub_gpafa [] trans_list

let step () =
  if not !is_paused then
  (
  let possible_actions = 
    let returned_list = ref [] in 
    (* NOTE:
       /!\ : Si on a des fonctions avec plus d'argument que le nombre de proc, 
       il y a de très fort risque d'avoir un comportement inatendu. 
       Il faudrait peut être mettre un warning et crash. 
    *)
    let (trans_map, trans_table) = Model.get_trans (get_model ()) in
    let test_transition arg_number trans_list =
      if arg_number > get_nb_proc () then failwith (Format.sprintf "At least %d proc is required for this simulation." (get_nb_proc ()))
      else
      let arg_list = get_args arg_number in
      List.iter (fun arg -> returned_list := (get_possible_action_for_arg arg trans_list trans_map)@(!returned_list)) arg_list
    in
    IntMap.iter test_transition trans_table;
    !returned_list
  in
  if List.length possible_actions > 0 then
      (
      let (arg, ac, name) = get_random_in_list possible_actions in
      ac arg;         
      let ntr = ((name, arg), Utils.get_model_state ()) in 
      Traces.add full_trace ntr;
      )
  );
  on_model_change_callback ()

(* Interaction functions *)

let lock_trans trans_name =
  Hashtbl.add runtime_lock trans_name (fun _ -> false)

let unlock_trans trans_name =
  Hashtbl.remove runtime_lock trans_name

let toggle_pause () = is_paused := not (!is_paused)

let take_step_back () =
  Traces.prev full_trace;
  let (_, ms) = Traces.get full_trace in
  Model.set_state (get_model ()) ms

let take_step_forward () = 
  let pre_paused = !is_paused in
  is_paused := false;
  step ();
  is_paused := pre_paused

let reset () = init ()

let get_model_state () =
  let (_, ret) = Traces.get full_trace in ret

(* Scene functions *)

let get_vuv_for_const () =
  let mstate = get_model_state () in
  let ret = ref [] in
  let add_vars vname = function
  | Traces.Val(v) -> 
    ret := (vname, v)::(!ret)
  | _ -> ()
  in
  StringMap.iter add_vars mstate;
  !ret

let get_vuv_for_proc i =
  let mstate = get_model_state () in
  let ret = ref [] in
  let add_vars vname = function 
    | Traces.Arr(a) -> ret := (vname, List.nth a i)::(!ret)
    | _ -> ()
  in
  StringMap.iter add_vars mstate;
  !ret

let get_vuv_for_proc_pair i j = 
  let mstate = get_model_state () in
  let ret = ref [] in
  let add_vars vname = function
    | Traces.Mat(m) -> 
        let a = List.nth m i in
        ret := (vname, List.nth a j)::(!ret)
    | _ -> ()
  in
  StringMap.iter add_vars mstate;
  !ret

let get_vuv vuv_name = StringMap.find vuv_name (get_model_state ())

let take_transition tname args = 
  let (trans_map, _) = Model.get_trans (get_model ()) in
  let (req, ac) = StringMap.find tname trans_map in
  if req args then (ac args; on_model_change_callback ())
