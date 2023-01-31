open Utils
open Format

let build_model () =
let state = ["Idle" ; "Wait" ; "Use"] in
let msg = ["Empty" ; "Req" ; "Ack" ; "Ok"] in

let vTimer = ref 0. in
let vTick = ref 0. in
let vState = Array.make (get_nb_proc ()) ("Idle") in
let vClock = Array.make (get_nb_proc ()) (0.) in
let vLast = Array.make (get_nb_proc ()) (0.) in
let vChannel_msg = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) ("Empty")) in
let vChannel_timestamp = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) (0.)) in

let var_as_string name want = match name with
	| "Timer" -> 
		sprintf "%f" (!vTimer)
	| "State" -> 
		let result = ref "" in 
		result := (!result)^"[ ";
		for tmp_0 = 0 to (get_nb_proc () - 1) do 
			result := (!result)^sprintf"%s "(vState.(tmp_0))
		done;
		result := (!result)^"]";
		!result
	| "Clock" -> 
		let result = ref "" in 
		result := (!result)^"[ ";
		for tmp_0 = 0 to (get_nb_proc () - 1) do 
			result := (!result)^sprintf"%f "(vClock.(tmp_0))
		done;
		result := (!result)^"]";
		!result
	| "Last" -> 
		let result = ref "" in 
		result := (!result)^"[ ";
		for tmp_0 = 0 to (get_nb_proc () - 1) do 
			result := (!result)^sprintf"%f "(vLast.(tmp_0))
		done;
		result := (!result)^"]";
		!result
	| "Channel_msg" -> 
		let result = ref "" in 
		result := (!result)^"[ ";
		for tmp_0 = 0 to (get_nb_proc () - 1) do 
			result := (!result)^"[ ";
			for tmp_1 = 0 to (get_nb_proc () - 1) do 
				result := (!result)^sprintf"%s "(vChannel_msg.(tmp_0).(tmp_1))
			done;
			result := (!result)^"]";
		done;
		result := (!result)^"]";
		!result
	| "Channel_timestamp" -> 
		let result = ref "" in 
		result := (!result)^"[ ";
		for tmp_0 = 0 to (get_nb_proc () - 1) do 
			result := (!result)^"[ ";
			for tmp_1 = 0 to (get_nb_proc () - 1) do 
				result := (!result)^sprintf"%f "(vChannel_timestamp.(tmp_0).(tmp_1))
			done;
			result := (!result)^"]";
		done;
		result := (!result)^"]";
		!result
	| "Tick" -> 
		sprintf "%f" (!vTick)
	| _ -> raise Not_found
in
let dump_vars () =
	printf "----------Current State----------\n";
	printf "Timer = %s\n" (var_as_string "Timer" []);
	printf "State = %s\n" (var_as_string "State" []);
	printf "Clock = %s\n" (var_as_string "Clock" []);
	printf "Last = %s\n" (var_as_string "Last" []);
	printf "Channel_msg = %s\n" (var_as_string "Channel_msg" []);
	printf "Channel_timestamp = %s\n" (var_as_string "Channel_timestamp" []);
	printf "Tick = %s\n" (var_as_string "Tick" []);
	printf "---------------------------------\n%!"
in

let init () = 
	vTick := Random.float max_float;
	vTimer := 1.;
	for tmp_0 = 0 to (get_nb_proc () - 1) do 
		vState.(tmp_0) <- "Idle";
		vClock.(tmp_0) <- Random.float max_float;
		vLast.(tmp_0) <- Random.float max_float;
		for tmp_1 = 0 to (get_nb_proc () - 1) do 
			vChannel_msg.(tmp_0).(tmp_1) <- "Empty";
			vChannel_timestamp.(tmp_0).(tmp_1) <- Random.float max_float;
		done;
	done;
	()
in

let req_t3 args = 
	let z = List.nth args 0 in
	vState.(z) = "Wait" && 
	(forall_other (fun j -> vChannel_msg.(z).(j) = "Ok" && true) args) && 
	true
in

let ac_t3 args = 
	let z = List.nth args 0 in
	let nState = Array.make (get_nb_proc ()) ("Idle") in
	for _j9 = 0 to ((get_nb_proc ()) - 1) do 
 		nState.(_j9) <- if _j9 = z && true then "Use" else vState.(_j9)
	done; 
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vState.(tmp_0) <- nState.(tmp_0);
	done;
	()
in

let t3 = ("t3", req_t3, ac_t3) 
in

let req_t4 args = 
	let z = List.nth args 0 in
	0. < !(vTick) && vState.(z) = "Use" && 
	true
in

let ac_t4 args = 
	let z = List.nth args 0 in
	let nTimer = !(vTimer) +. !(vTick) in 
	let nState = Array.make (get_nb_proc ()) ("Idle") in
	for _j10 = 0 to ((get_nb_proc ()) - 1) do 
 		nState.(_j10) <- if _j10 = z && true then "Idle" else vState.(_j10)
	done; 
	let nClock = Array.make (get_nb_proc ()) (0.) in
	for _j11 = 0 to ((get_nb_proc ()) - 1) do 
 		nClock.(_j11) <- if _j11 = z && true then !(vTimer) else vClock.(_j11)
	done; 
	let nChannel_msg = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) ("Empty")) in
	for s = 0 to ((get_nb_proc ()) - 1) do 
 		for r = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_msg.(s).(r) <- if s = z && vChannel_msg.(s).(r) = "Ok" && true then "Empty" else if r = z && vChannel_msg.(s).(r) = "Req" && true then "Ack" else vChannel_msg.(s).(r)
		done; 
	done; 
	let nChannel_timestamp = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) (0.)) in
	for s = 0 to ((get_nb_proc ()) - 1) do 
 		for r = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_timestamp.(s).(r) <- if r = z && vChannel_msg.(s).(r) = "Req" && true then !(vTimer) else vChannel_timestamp.(s).(r)
		done; 
	done; 
	vTimer := nTimer;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vClock.(tmp_0) <- nClock.(tmp_0);
		vState.(tmp_0) <- nState.(tmp_0);
		for tmp_1 = 0 to ((get_nb_proc ()) - 1) do 
			vChannel_timestamp.(tmp_0).(tmp_1) <- nChannel_timestamp.(tmp_0).(tmp_1);
			vChannel_msg.(tmp_0).(tmp_1) <- nChannel_msg.(tmp_0).(tmp_1);
		done;
	done;
	()
in

let t4 = ("t4", req_t4, ac_t4) 
in

let req_t1 args = 
	let z = List.nth args 0 in
	0. < !(vTick) && vState.(z) = "Idle" && 
	true
in

let ac_t1 args = 
	let z = List.nth args 0 in
	let nTimer = !(vTimer) +. !(vTick) in 
	let nState = Array.make (get_nb_proc ()) ("Idle") in
	for _j1 = 0 to ((get_nb_proc ()) - 1) do 
 		nState.(_j1) <- if _j1 = z && true then "Wait" else vState.(_j1)
	done; 
	let nClock = Array.make (get_nb_proc ()) (0.) in
	for _j2 = 0 to ((get_nb_proc ()) - 1) do 
 		nClock.(_j2) <- if _j2 = z && true then !(vTimer) else vClock.(_j2)
	done; 
	let nLast = Array.make (get_nb_proc ()) (0.) in
	for _j3 = 0 to ((get_nb_proc ()) - 1) do 
 		nLast.(_j3) <- if _j3 = z && true then !(vTimer) else vLast.(_j3)
	done; 
	let nChannel_msg = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) ("Empty")) in
	for s = 0 to ((get_nb_proc ()) - 1) do 
 		for r = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_msg.(s).(r) <- if s = z && vChannel_msg.(s).(r) = "Empty" && true then "Req" else vChannel_msg.(s).(r)
		done; 
	done; 
	let nChannel_timestamp = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) (0.)) in
	for s = 0 to ((get_nb_proc ()) - 1) do 
 		for r = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_timestamp.(s).(r) <- if s = z && vChannel_msg.(s).(r) = "Empty" && true then !(vTimer) else vChannel_timestamp.(s).(r)
		done; 
	done; 
	vTimer := nTimer;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vLast.(tmp_0) <- nLast.(tmp_0);
		vClock.(tmp_0) <- nClock.(tmp_0);
		vState.(tmp_0) <- nState.(tmp_0);
		for tmp_1 = 0 to ((get_nb_proc ()) - 1) do 
			vChannel_timestamp.(tmp_0).(tmp_1) <- nChannel_timestamp.(tmp_0).(tmp_1);
			vChannel_msg.(tmp_0).(tmp_1) <- nChannel_msg.(tmp_0).(tmp_1);
		done;
	done;
	()
in

let t1 = ("t1", req_t1, ac_t1) 
in

let req_t2 args = 
	let z = List.nth args 0 in
	let r = List.nth args 1 in
	0. < !(vTick) && vState.(z) = "Wait" && vChannel_msg.(z).(r) = "Ack" && 
	true
in

let ac_t2 args = 
	let z = List.nth args 0 in
	let r = List.nth args 1 in
	let nTimer = !(vTimer) +. !(vTick) in 
	let nClock = Array.make (get_nb_proc ()) (0.) in
	for _j4 = 0 to ((get_nb_proc ()) - 1) do 
 		nClock.(_j4) <- if _j4 = z && true then !(vTimer) else vClock.(_j4)
	done; 
	let nChannel_msg = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) ("Empty")) in
	for _j5 = 0 to ((get_nb_proc ()) - 1) do 
 		for _j6 = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_msg.(_j5).(_j6) <- if _j5 = z && _j6 = r && true then "Ok" else vChannel_msg.(_j5).(_j6)
		done; 
	done; 
	let nChannel_timestamp = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) (0.)) in
	for _j7 = 0 to ((get_nb_proc ()) - 1) do 
 		for _j8 = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_timestamp.(_j7).(_j8) <- if _j7 = z && _j8 = r && true then !(vTimer) else vChannel_timestamp.(_j7).(_j8)
		done; 
	done; 
	vTimer := nTimer;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vClock.(tmp_0) <- nClock.(tmp_0);
		for tmp_1 = 0 to ((get_nb_proc ()) - 1) do 
			vChannel_timestamp.(tmp_0).(tmp_1) <- nChannel_timestamp.(tmp_0).(tmp_1);
			vChannel_msg.(tmp_0).(tmp_1) <- nChannel_msg.(tmp_0).(tmp_1);
		done;
	done;
	()
in

let t2 = ("t2", req_t2, ac_t2) 
in

let req_t5 args = 
	let z = List.nth args 0 in
	let s = List.nth args 1 in
	0. < !(vTick) && vState.(z) = "Idle" && vChannel_msg.(s).(z) = "Req" && vChannel_timestamp.(s).(z) < vClock.(z) && 
	true
in

let ac_t5 args = 
	let z = List.nth args 0 in
	let s = List.nth args 1 in
	let nTimer = !(vTimer) +. !(vTick) in 
	let nClock = Array.make (get_nb_proc ()) (0.) in
	for _j12 = 0 to ((get_nb_proc ()) - 1) do 
 		nClock.(_j12) <- if _j12 = z && true then !(vTimer) else vClock.(_j12)
	done; 
	let nChannel_msg = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) ("Empty")) in
	for _j13 = 0 to ((get_nb_proc ()) - 1) do 
 		for _j14 = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_msg.(_j13).(_j14) <- if _j13 = s && _j14 = z && true then "Ack" else vChannel_msg.(_j13).(_j14)
		done; 
	done; 
	let nChannel_timestamp = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) (0.)) in
	for _j15 = 0 to ((get_nb_proc ()) - 1) do 
 		for _j16 = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_timestamp.(_j15).(_j16) <- if _j15 = s && _j16 = z && true then !(vTimer) else vChannel_timestamp.(_j15).(_j16)
		done; 
	done; 
	vTimer := nTimer;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vClock.(tmp_0) <- nClock.(tmp_0);
		for tmp_1 = 0 to ((get_nb_proc ()) - 1) do 
			vChannel_timestamp.(tmp_0).(tmp_1) <- nChannel_timestamp.(tmp_0).(tmp_1);
			vChannel_msg.(tmp_0).(tmp_1) <- nChannel_msg.(tmp_0).(tmp_1);
		done;
	done;
	()
in

let t5 = ("t5", req_t5, ac_t5) 
in

let req_t6 args = 
	let z = List.nth args 0 in
	let s = List.nth args 1 in
	0. < !(vTick) && vState.(z) = "Wait" && vChannel_msg.(s).(z) = "Req" && vChannel_timestamp.(s).(z) < vLast.(z) && 
	true
in

let ac_t6 args = 
	let z = List.nth args 0 in
	let s = List.nth args 1 in
	let nTimer = !(vTimer) +. !(vTick) in 
	let nClock = Array.make (get_nb_proc ()) (0.) in
	for _j17 = 0 to ((get_nb_proc ()) - 1) do 
 		nClock.(_j17) <- if _j17 = z && true then !(vTimer) else vClock.(_j17)
	done; 
	let nChannel_msg = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) ("Empty")) in
	for _j18 = 0 to ((get_nb_proc ()) - 1) do 
 		for _j19 = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_msg.(_j18).(_j19) <- if _j18 = s && _j19 = z && true then "Ack" else vChannel_msg.(_j18).(_j19)
		done; 
	done; 
	let nChannel_timestamp = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) (0.)) in
	for _j20 = 0 to ((get_nb_proc ()) - 1) do 
 		for _j21 = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_timestamp.(_j20).(_j21) <- if _j20 = s && _j21 = z && true then !(vTimer) else vChannel_timestamp.(_j20).(_j21)
		done; 
	done; 
	vTimer := nTimer;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vClock.(tmp_0) <- nClock.(tmp_0);
		for tmp_1 = 0 to ((get_nb_proc ()) - 1) do 
			vChannel_timestamp.(tmp_0).(tmp_1) <- nChannel_timestamp.(tmp_0).(tmp_1);
			vChannel_msg.(tmp_0).(tmp_1) <- nChannel_msg.(tmp_0).(tmp_1);
		done;
	done;
	()
in

let t6 = ("t6", req_t6, ac_t6) 
in

let req_t7 args = 
	let z = List.nth args 0 in
	let s = List.nth args 1 in
	0. < !(vTick) && s < z && vState.(z) = "Wait" && vChannel_msg.(s).(z) = "Req" && vChannel_timestamp.(s).(z) = vLast.(z) && 
	true
in

let ac_t7 args = 
	let z = List.nth args 0 in
	let s = List.nth args 1 in
	let nTimer = !(vTimer) +. !(vTick) in 
	let nClock = Array.make (get_nb_proc ()) (0.) in
	for _j22 = 0 to ((get_nb_proc ()) - 1) do 
 		nClock.(_j22) <- if _j22 = z && true then !(vTimer) else vClock.(_j22)
	done; 
	let nChannel_msg = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) ("Empty")) in
	for _j23 = 0 to ((get_nb_proc ()) - 1) do 
 		for _j24 = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_msg.(_j23).(_j24) <- if _j23 = s && _j24 = z && true then "Ack" else vChannel_msg.(_j23).(_j24)
		done; 
	done; 
	let nChannel_timestamp = Array.make (get_nb_proc ()) (Array.make (get_nb_proc ()) (0.)) in
	for _j25 = 0 to ((get_nb_proc ()) - 1) do 
 		for _j26 = 0 to ((get_nb_proc ()) - 1) do 
 			nChannel_timestamp.(_j25).(_j26) <- if _j25 = s && _j26 = z && true then !(vTimer) else vChannel_timestamp.(_j25).(_j26)
		done; 
	done; 
	vTimer := nTimer;
	for tmp_0 = 0 to ((get_nb_proc ()) - 1) do 
		vClock.(tmp_0) <- nClock.(tmp_0);
		for tmp_1 = 0 to ((get_nb_proc ()) - 1) do 
			vChannel_timestamp.(tmp_0).(tmp_1) <- nChannel_timestamp.(tmp_0).(tmp_1);
			vChannel_msg.(tmp_0).(tmp_1) <- nChannel_msg.(tmp_0).(tmp_1);
		done;
	done;
	()
in

let t7 = ("t7", req_t7, ac_t7) 
in


let mymodel = ref Model.empty in

mymodel := Model.add_trans 1 t3 (!mymodel);
mymodel := Model.add_trans 1 t4 (!mymodel);
mymodel := Model.add_trans 1 t1 (!mymodel);
mymodel := Model.add_trans 2 t2 (!mymodel);
mymodel := Model.add_trans 2 t5 (!mymodel);
mymodel := Model.add_trans 2 t6 (!mymodel);
mymodel := Model.add_trans 2 t7 (!mymodel);
mymodel := Model.set_init init (!mymodel);
mymodel := Model.set_vars ([], var_as_string) (!mymodel);
register_dumper dump_vars;
set_model (!mymodel)
