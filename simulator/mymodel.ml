open Utils
open Maps
open Model
open Traces
open Format

let build_model () =
let msg = ["Empty" ; "Reqs" ; "Reqe"] in
let state = ["Invalid" ; "Shared" ; "Exclusive"] in

let vExgntd = ref true in
let vCurcmd = ref "Empty" in
let vCurptr = ref 0 in
let vCache = Array.make (get_nb_proc ()) ("Invalid") in
let vShrset = Array.make (get_nb_proc ()) (true) in

let state_getter () = 
	let ret = ref StringMap.empty in 
	let add_to_ret n v = ret := StringMap.add n v (!ret) in 
	add_to_ret "Exgntd" (Val(VBool(!vExgntd)));
	add_to_ret "Curcmd" (Val(VConstr(!vCurcmd)));
	add_to_ret "Curptr" (Val(VInt(!vCurptr)));
	add_to_ret "Cache" (Arr(List.map (fun x -> VConstr(x)) (Array.to_list vCache)));
	add_to_ret "Shrset" (Arr(List.map (fun x -> VBool(x)) (Array.to_list vShrset)));
	!ret
in

let state_setter state = 
	let set_vuv vname vval = 
		match vname, vval with 
			| "Exgntd", Val(VBool(v)) -> vExgntd := v
			| "Curcmd", Val(VConstr(v)) -> vCurcmd := v
			| "Curptr", Val(VInt(v)) -> vCurptr := v
			| "Cache", Arr(a) -> List.iteri (fun i x -> match x with | VConstr(v) -> vCache.(i) <- v | _ -> failwith "Unknown") a
			| "Shrset", Arr(a) -> List.iteri (fun i x -> match x with | VBool(v) -> vShrset.(i) <- v | _ -> failwith "Unknown") a
			| _, _ -> failwith "Unknown"
		in
	StringMap.iter set_vuv state
in

let init () = 
	vExgntd := false;
	vCurcmd := "Empty";
	vCurptr := get_random_proc ();
	for tmp_0 = 0 to (get_nb_proc () - 1) do 
		vShrset.(tmp_0) <- false;
		vCache.(tmp_0) <- "Invalid";
	done;
	()
in

let unsafe_0 args = 
	let z1 = List.nth args 0 in
	let z2 = List.nth args 1 in
	vCache.(z1) = "Exclusive" &&
	vCache.(z2) = "Shared" &&
	true
in

let req_req_shared args = 
	let n = List.nth args 0 in
	!(vCurcmd) = "Empty" && vCache.(n) = "Invalid" && 
	true
in

let ac_req_shared args = 
	let n = List.nth args 0 in
	let nCurcmd = "Reqs" in 
	let nCurptr = n in 
	vCurptr := nCurptr;
	vCurcmd := nCurcmd;
	()
in

let req_shared = ("req_shared", req_req_shared, ac_req_shared) 
in

let req_req_exclusive args = 
	let n = List.nth args 0 in
	!(vCurcmd) = "Empty" && vCache.(n) <> "Exclusive" && 
	true
in

let ac_req_exclusive args = 
	let n = List.nth args 0 in
	let nCurcmd = "Reqe" in 
	let nCurptr = n in 
	vCurptr := nCurptr;
	vCurcmd := nCurcmd;
	()
in

let req_exclusive = ("req_exclusive", req_req_exclusive, ac_req_exclusive) 
in

let req_inv_1 args = 
	let n = List.nth args 0 in
	!(vCurcmd) = "Reqe" && vShrset.(n) = true && 
	true
in

let ac_inv_1 args = 
	let n = List.nth args 0 in
	let nExgntd = false in 
	let nCache = Array.make (get_nb_proc ()) ("Invalid") in
	for _j1 = 0 to ((get_nb_proc ()) - 1) do 
 		nCache.(_j1) <- if _j1 = n && true then "Invalid" else vCache.(_j1)
	done; 
	let nShrset = Array.make (get_nb_proc ()) (true) in
	for _j2 = 0 to ((get_nb_proc ()) - 1) do 
 		nShrset.(_j2) <- if _j2 = n && true then false else vShrset.(_j2)
	done; 
	vExgntd := nExgntd;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vShrset.(tmp_0) <- nShrset.(tmp_0);
		vCache.(tmp_0) <- nCache.(tmp_0);
	done;
	()
in

let inv_1 = ("inv_1", req_inv_1, ac_inv_1) 
in

let req_inv_2 args = 
	let n = List.nth args 0 in
	!(vExgntd) = true && !(vCurcmd) = "Reqs" && vShrset.(n) = true && 
	true
in

let ac_inv_2 args = 
	let n = List.nth args 0 in
	let nExgntd = false in 
	let nCache = Array.make (get_nb_proc ()) ("Invalid") in
	for _j3 = 0 to ((get_nb_proc ()) - 1) do 
 		nCache.(_j3) <- if _j3 = n && true then "Invalid" else vCache.(_j3)
	done; 
	let nShrset = Array.make (get_nb_proc ()) (true) in
	for _j4 = 0 to ((get_nb_proc ()) - 1) do 
 		nShrset.(_j4) <- if _j4 = n && true then false else vShrset.(_j4)
	done; 
	vExgntd := nExgntd;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vShrset.(tmp_0) <- nShrset.(tmp_0);
		vCache.(tmp_0) <- nCache.(tmp_0);
	done;
	()
in

let inv_2 = ("inv_2", req_inv_2, ac_inv_2) 
in

let req_gnt_shared args = 
	let n = List.nth args 0 in
	!(vExgntd) = false && !(vCurcmd) = "Reqs" && !(vCurptr) = n && 
	true
in

let ac_gnt_shared args = 
	let n = List.nth args 0 in
	let nCurcmd = "Empty" in 
	let nShrset = Array.make (get_nb_proc ()) (true) in
	for _j5 = 0 to ((get_nb_proc ()) - 1) do 
 		nShrset.(_j5) <- if _j5 = n && true then true else vShrset.(_j5)
	done; 
	let nCache = Array.make (get_nb_proc ()) ("Invalid") in
	for _j6 = 0 to ((get_nb_proc ()) - 1) do 
 		nCache.(_j6) <- if _j6 = n && true then "Shared" else vCache.(_j6)
	done; 
	vCurcmd := nCurcmd;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vCache.(tmp_0) <- nCache.(tmp_0);
		vShrset.(tmp_0) <- nShrset.(tmp_0);
	done;
	()
in

let gnt_shared = ("gnt_shared", req_gnt_shared, ac_gnt_shared) 
in

let req_gnt_exclusive args = 
	let n = List.nth args 0 in
	!(vExgntd) = false && !(vCurcmd) = "Reqe" && !(vCurptr) = n && vShrset.(n) = false && 
	(forall_other (fun l -> vShrset.(l) = false && true) args) && 
	true
in

let ac_gnt_exclusive args = 
	let n = List.nth args 0 in
	let nCurcmd = "Empty" in 
	let nExgntd = true in 
	let nShrset = Array.make (get_nb_proc ()) (true) in
	for _j7 = 0 to ((get_nb_proc ()) - 1) do 
 		nShrset.(_j7) <- if _j7 = n && true then true else vShrset.(_j7)
	done; 
	let nCache = Array.make (get_nb_proc ()) ("Invalid") in
	for _j8 = 0 to ((get_nb_proc ()) - 1) do 
 		nCache.(_j8) <- if _j8 = n && true then "Exclusive" else vCache.(_j8)
	done; 
	vCurcmd := nCurcmd;
	vExgntd := nExgntd;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vCache.(tmp_0) <- nCache.(tmp_0);
		vShrset.(tmp_0) <- nShrset.(tmp_0);
	done;
	()
in

let gnt_exclusive = ("gnt_exclusive", req_gnt_exclusive, ac_gnt_exclusive) 
in


let mymodel = ref Model.empty in

mymodel := Model.add_trans 1 req_shared (!mymodel);
mymodel := Model.add_trans 1 req_exclusive (!mymodel);
mymodel := Model.add_trans 1 inv_1 (!mymodel);
mymodel := Model.add_trans 1 inv_2 (!mymodel);
mymodel := Model.add_trans 1 gnt_shared (!mymodel);
mymodel := Model.add_trans 1 gnt_exclusive (!mymodel);
mymodel := Model.set_init init (!mymodel);
mymodel := Model.set_vars ([], state_getter, state_setter) (!mymodel);
set_model (!mymodel)
