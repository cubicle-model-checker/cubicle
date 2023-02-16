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
  let print_val val_name val_value =
    printf "%s : " val_name;
    let pval v = printf "%s " (Model.vuv_to_string v)
    in
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
  StringMap.iter print_val mstate;
  printf "-------- END DUMP --------\n%!"

let print_list_int l =
  Format.printf "[ ";
  List.iter (fun i -> Format.printf "%i " i) l;
  Format.printf "]\n\n"

(* Simulation functions *)

let get_random_in_list l =
  List.nth l (Random.int (List.length l))

let get_random_proc () =
  Random.int (get_nb_proc ())

(* Renvoie toutes les combinaisons possible de n éléments parmi nb_proc(), ne contenant pas deux fois le même élément *)
let computed_args = Hashtbl.create 124 

let rec get_args n =
  try Hashtbl.find computed_args n with Not_found ->
    (
      if n < 0 || n > (get_nb_proc ()) then assert false else (* TODO : Remplacer le assert false ici par une erreur indiquant que le nombre de nbproc doit être supérieur a ... *)
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

(* Fonction d'aide pour transitions *)
let forall_other f i = 
  let rec forall_sub n =
    if not (List.exists (fun v -> v = n) i) && not (f n) then false else if n == ((get_nb_proc ()) - 1) then true else forall_sub (n+1) in
  forall_sub 0

let forall f = forall_other f []
