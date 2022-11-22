let nb_proc = ref 1000 (* Note : La valeur initiale est la valeur maximale autorisée actuellement *)
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
(*
* Note : C'est actuellement très crade et donc a refaire. 
*)
let rec get_args n =
  if n < 0 || n > (get_nb_proc ()) then assert false else
  let rec sub_get_args cur prec returned = 
    let tmp_returned' = (List.map (fun l_part -> if cur > List.hd l_part then l_part@[cur] else []) prec) in
    let tmp_tmp_returned' = List.filter (fun l -> List.length l > 0) tmp_returned' in
    let returned' = tmp_tmp_returned'@returned in
    if cur < (get_nb_proc () - 1) then sub_get_args (cur+1) prec returned' else returned'
  in

  match n with
  | 0 -> []
  | 1 -> let rec nul c l = if c < get_nb_proc () then nul (c+1) ([c]::l) else l in nul 0 []
  | _ -> let prec = get_args (n-1) in sub_get_args 0 prec []

let rec combi n =
  if n < 0 then assert false else
  let rec sub_combi cur l l_returned =
  let l_returned' = (List.map (fun l_part -> cur::l_part) l)@l_returned in
    if cur < (get_nb_proc () - 1) then sub_combi (cur+1) l l_returned' else l_returned'
    in
  
    match n with
    | 0 -> []
    | 1 -> let rec nul c l = if c < get_nb_proc () then nul (c+1) ([c]::l) else l in nul 0 []
    | _ -> let prec = combi (n-1) in sub_combi 0 prec []

(* Transitions *)
type transition = string*(int list -> bool) * (int list -> unit)

let req_aq_table : (int, transition list) Hashtbl.t = Hashtbl.create (get_nb_proc ())

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

(** NOTE : Pourrait on utiliser un Set ici ? *)
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
      Format.printf "Added event %s" (event_to_string e);
      Format.print_newline ();
      event_list := (!event_list)@[e] (* La raison d'utiliser un add est que c'est plus pratique si on veut changer le fonctionnement des event*)
    )

let remove_event e = 
  let rec sub_removed prec reste = 
    match reste with
    | (hd::tl) -> if hd = e then sub_removed prec tl else sub_removed (prec@[hd]) tl
    | _ -> prec
  in
  event_list := sub_removed [] (!event_list)

(* Simulation *)

let get_possible_action_for_arg trans_list arg =
  let rec sub_gpafa remain returned =
    match remain with
    | [] -> returned
    | (name, req, ac) :: remain' -> if req arg then sub_gpafa remain' ((arg, ac, name)::returned) else sub_gpafa remain' returned
  in
  sub_gpafa trans_list []

let step () = 
  let possible_actions = 
    let returned_list = ref [] in
    for i = 0 to get_nb_proc () do
      if Hashtbl.mem req_aq_table i then
      let arg_list = get_args i in
      let trans_list = Hashtbl.find req_aq_table i in
      List.iter (fun arg -> returned_list := (get_possible_action_for_arg trans_list arg)@(!returned_list)) arg_list
    done;
    !returned_list
  in
  if List.length possible_actions > 0 then
    (
    let (arg, ac, name) = get_random_in_list possible_actions in
    ac arg;
    Format.printf "%s " name;
    print_list_int arg
    )
