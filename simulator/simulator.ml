open Utils

(* -- Interaction -- *)

(* Lock is similar to req but it is created at runtime *)
let runtime_lock : (string, (int list -> bool)) Hashtbl.t = Hashtbl.create 10

let lock_trans trans_name =
  Hashtbl.add runtime_lock trans_name (fun _ -> false)

let unlock_trans trans_name =
  Hashtbl.remove runtime_lock trans_name

(* -- Simulation -- *)

let full_trace : Model.full_trace ref = ref ([], [])
let get_full_trace () = !full_trace

let init () =
  Random.init (int_of_float (Unix.time ()));
  let (_,minit,_) = get_model () in
  full_trace := (get_model_state (), []);
  minit ();
  
  dumper ()

let get_possible_action_for_arg arg trans_list trans_map = 
  let sub_gpafa returned name = 
    let (req, ac) = Model.StringMap.find name trans_map in
    let lock      = try Hashtbl.find runtime_lock name with Not_found -> (fun _ -> true) in
    if (req arg && lock arg) then ((arg,ac,name)::returned) else returned in
  List.fold_left sub_gpafa [] trans_list

let step () =
  let possible_actions = 
    let returned_list = ref [] in 
    (* NOTE:
       /!\ : Si on a des fonctions avec plus d'argument que le nombre de proc, 
       il y a de très fort risque d'avoir un comportement inatendu. 
       Il faudrait peut être mettre un warning et crash. 
    *)
    let (_, _, (trans_map, trans_table)) = get_model () in
    let test_transition arg_number trans_list = 
      let arg_list = get_args arg_number in 
      List.iter (fun arg -> returned_list := (get_possible_action_for_arg arg trans_list trans_map)@(!returned_list)) arg_list
    in
    Model.IntMap.iter test_transition trans_table;
    !returned_list
  in
  begin if List.length possible_actions > 0 then
      (
      let (arg, ac, name) = get_random_in_list possible_actions in
      ac arg;                                     (* Effectue l'action *)
      let (init, last_trace) = !full_trace in
      full_trace := (init, ((name, arg),get_model_state ())::last_trace);
      Format.printf "Took %s with args " name;    (* Affiche une trace de l'action dans la sortie standard*)
      print_list_int arg;
      )
    else Format.printf "No possible transition from current state\n"
  end;
  Format.printf "New state : \n";
  dumper ();
  Format.printf "\n%!";
