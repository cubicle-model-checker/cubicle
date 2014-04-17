

exception Unsafe of Node.t

(*************************************************)
(* Safety check : s /\ init must be inconsistent *)
(*************************************************)
    
let dnf_safe sa = List.for_all (inconsistent_2cubes sa)

let cdnf_asafe ua =
  List.exists (
    List.for_all (fun a ->
      inconsistent_array (Array.append ua a)))

let obviously_safe { t_unsafe = args,_ ; t_arru = ua } =
  let _, cdnf_ai = Hashtbl.find init_instances (List.length args) in
  cdnf_asafe ua cdnf_ai
 
let check_safety s =
  (*Debug.unsafe s;*)
  try
    if not (obviously_safe s) then
      begin
	Prover.unsafe s;
	if not quiet then eprintf "\nUnsafe trace: @[%a@]@." 
	  Pretty.print_verbose_node s;
        raise (Search.Unsafe s)
      end
  with
    | Smt.Unsat _ -> ()

