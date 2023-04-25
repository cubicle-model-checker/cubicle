(* 
   TODO :
  - Add number of proc to trace
  - Verify out of bound in get and next
  - Add a "max" parameter ? You can then have where you are and where you should stop. Adding to a trace increase max. You can 'forget' everything after a certain ...
*)
open Maps

type var_unit_value = 
  | VInt        of int
  | VFloat      of float
  | VBool       of bool
  | VConstr     of string
  | VLock       of int option
  | VRlock      of int option * int
  | VSemaphore  of int

type var_value = 
  | Val  of var_unit_value
  | Arr  of var_unit_value list
  | Mat  of var_unit_value list list

type model_state = var_value StringMap.t            (* name of var * value list *)

type tstep = (string * int list) * model_state      (* name of transition taken to get here, args, state after transition was taken *)
type t = (int ref) * (tstep Array.t ref)

let start (i, st) j = i := j 

let get (i, st) =
  if !i >= Array.length !st then failwith "(Traces) Out of bounds.";
  (!st).(!i)

let current_step (i, st) = !i

let next (i, st) = 
  if !i +1 < Array.length (!st) then i := !i + 1

let prev (i, st) = 
  if !i - 1 >= 0 then i := !i - 1

let position (i,_) = !i

let add (i, st) tr =
  let j = (!i)+1 in
  let t = Array.length (!st) in
  if j < t then
    (
      (!st).(j) <- tr
    )
  else 
    (
      let nst = Array.init ((t+1)*2) (fun x -> if x < (!i) then (!st).(x) else tr) in
      st := nst
    );
  i := j

let empty () = (ref 0, ref [||])

let save ((i, st) : t) (fmt : Format.formatter) =
  let open Format in
  for j=0 to !i do
    let ((tname, targs), _) = !st.(j) in
    fprintf fmt "%s" tname;
    if List.length targs > 0 then 
      (
      fprintf fmt " | args :";
      List.iter (fun x -> fprintf fmt " %d" x) targs;
      );
    fprintf fmt "\n";
  done;
  fprintf fmt "%!"
