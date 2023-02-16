(* 
   TODO :
  - Add number of proc to trace
  - Add init state to trace
  - Verify out of bound in get and next
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
  if !i >= Array.length !st then failwith "Trying to get out of bounds.";
  (!st).(!i)

let next (i, st) = 
  if !i +1 < Array.length (!st) then i := !i + 1

let prev (i, st) = 
  if !i - 1 >= 0 then i := !i - 1

let position (i,_) = !i

let add (i, st) tr =
  let j = (!i)+1 in
  let t = Array.length (!st) in
  if j < t then
    (!st).(j) <- tr
  else
    let nst = Array.init (t*2) (fun x -> if x < j then (!st).(x) else tr) in
    st := nst

let empty () = (ref 0, ref [||])


