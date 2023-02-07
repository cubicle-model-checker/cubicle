open Utils
open Model

let get_vuv_for_const =
  let mstate = Model.get_state (get_model ()) in
  let ret = ref [] in
  let add_vars (vname, vval) = match vval with
  | Val(v) -> 
    ret := (vname, v)::(!ret)
  | _ -> ()
  in
  List.iter add_vars mstate;
  !ret

let get_vuv_for_proc i =
  let mstate = Model.get_state (get_model ()) in
  let ret = ref [] in
  let add_vars (vname, vval) = match vval with
    | Arr(a) -> ret := (vname, List.nth a i)::(!ret)
    | _ -> ()
  in
  List.iter add_vars mstate;
  !ret

let get_vuv_for_proc_pair i j = 
  let mstate = Model.get_state (get_model ()) in
  let ret = ref [] in
  let add_vars (vname, vval) = match vval with
    | Mat(m) -> 
        let a = List.nth m i in
        ret := (vname, List.nth a j)::(!ret)
    | _ -> ()
  in
  List.iter add_vars mstate;
  !ret
