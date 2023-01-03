let nb_proc = ref 1000 (* NOTE : La valeur initiale est la valeur maximale autorisée actuellement *)
let get_nb_proc () = !nb_proc

let rec find_ieme l i =
  match i with
  | 0 -> List.hd l
  | _ -> 
    match l with
    | _ :: tl -> find_ieme tl (i-1)
    |  _ -> assert false

let get_random_in_list l =
  find_ieme l (Random.int (List.length l))

let get_random_proc () =
  Random.int (get_nb_proc ())

(* Fonction de debug, a supprimer *)

let print_list_int l = 
  List.iter (fun i -> Format.printf "%i " i) l;
  Format.print_newline ()

(* Renvoie toutes les combinaisons possible de n éléments parmi nb_proc(), ne contenant pas deux fois le même élément *)
let computed_args = Hashtbl.create 124 

let rec get_args n =
  try Hashtbl.find computed_args n with Not_found ->
    (
      if n < 0 || n > (get_nb_proc ()) then assert false else
        let rec sub_get_args cur prec returned = 
        let tmp_returned' = (List.map (fun l_part -> if cur > List.hd l_part then l_part@[cur] else []) prec) in
        let tmp_tmp_returned' = List.filter (fun l -> List.length l > 0) tmp_returned' in
        let returned' = tmp_tmp_returned'@returned in
        if cur < (get_nb_proc () - 1) then sub_get_args (cur+1) prec returned' else returned'
      in

      match n with
      | 0 -> [[]]
      | 1 -> let rec nul c l = if c < get_nb_proc () then nul (c+1) ([c]::l) else l in nul 0 []
      | _ -> 
          let prec = get_args (n-1) in 
          let result = sub_get_args 0 prec [] in 
          Hashtbl.add computed_args n result;
          result
    )
(* Transitions *)
type transition = string * (int list -> bool) * (int list -> unit) (* (nom_de_la_transition, transition_req, transition_ac) *)

let req_aq_table : (int, transition list) Hashtbl.t = Hashtbl.create (get_nb_proc ()) (* La req_aq_table associe un int (nombre d'arguments) a toutes les transitions prenant ce nombre d'argument *)

let add_req_acc nb_arg trans = 
  let cur = if Hashtbl.mem req_aq_table nb_arg then Hashtbl.find req_aq_table nb_arg else [] in
  Hashtbl.add req_aq_table nb_arg (trans::cur)
   
let forall_other f i = 
  let rec forall_sub n =
    if (n != i) && not (f n) then false else if n == ((get_nb_proc ()) - 1) then true else forall_sub (n+1) in
  forall_sub 0

let forall f = forall_other f (-1)

(* Gestion d'évènements *)

type event = 
  | Click of int
  | Button_down of char
  | Button_up of char
  | None

(* TODO : Utiliser un set ici. *)
let event_list = ref [None]

let event_to_string e=
match e with
| Click(i) -> Format.sprintf "Click (%d)" i
| Button_down(c) -> Format.sprintf "Button_Down (%c)" c
| Button_up(c) -> Format.sprintf "Button_Up (%c)" c
| _ -> ""

let exist_event e = List.exists (fun e' -> e = e') (!event_list)

let add_event e =
  if not (exist_event e) then
    (
      Printf.printf "Added event %s\n%!" (event_to_string e);
      event_list := (!event_list)@[e] 
    )

let remove_event e = 
  let rec sub_removed prec reste = 
    match reste with
    | (hd::tl) -> if hd = e then sub_removed prec tl else sub_removed (prec@[hd]) tl
    | _ -> prec
  in
  event_list := sub_removed [] (!event_list)

(* Simulation *)

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
    Hashtbl.iter test_transition req_aq_table;
    !returned_list
  in
  if List.length possible_actions > 0 then
    (
    let (arg, ac, name) = get_random_in_list possible_actions in
    ac arg;                     (* Effectue l'action *)
    Format.printf "%s " name;   (* Affiche une trace de l'action dans la sortie standard*)
    print_list_int arg;
    Format.print_newline ()
    )
  else Printf.printf "Pas d'action possible\n%!"

