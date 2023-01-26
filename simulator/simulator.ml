open Utils

let init () =
  let (_,_,minit,_) = get_model () in
  minit ();
  (!dumper) ()

let get_possible_action_for_arg arg trans_list = 
  let rec sub_gpafa returned (name, req, ac) = if req arg then ((arg,ac,name)::returned) else returned in
  List.fold_left sub_gpafa [] trans_list

let step () =
  let possible_actions = 
    let returned_list = ref [] in 
    (* Attention : Si on a des fonctions avec plus d'argument que le nombre de proc, il y a de très fort risque d'avoir un comportement inatendu. Il faudrait peut être mettre un warning et crash. *)
    let test_transition arg_number trans_list = 
      let arg_list = get_args arg_number in 
      List.iter (fun arg -> returned_list := (get_possible_action_for_arg arg trans_list)@(!returned_list)) arg_list
    in
    let (_,_, _, req_ac_table) = get_model () in
    Model.IntMap.iter test_transition req_ac_table;
    !returned_list
  in
  begin if List.length possible_actions > 0 then
      (
      let (arg, ac, name) = get_random_in_list possible_actions in
      ac arg;                                     (* Effectue l'action *)
      Format.printf "Took %s with args " name;    (* Affiche une trace de l'action dans la sortie standard*)
      print_list_int arg;
      )
    else Format.printf "Pas d'action possible\n"
  end;
  Format.printf "New state : \n";
  (!dumper) ();
  Format.printf "\n%!";
