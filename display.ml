(* DISPLAY METHODS AND MODULES TO MAKE HSTRING FROM AST TYPES *)

(* /!\ The methods hstring_of_* return a hstring list *)

let hstring_of_value value =
  match value with
    | Int i -> [Hstring.make (string_of_int i)]
    | Hstr h -> [h]
    | Proc p -> [Hstring.make (string_of_int p)]

let h_new_line = [Hstring.make "\n"]

let rec hstring_of_term t =
  match t with
    | Const c -> [Hstring.make (string_of_int (value_c c))]
    | Elem (e, _) -> [e]
    | Access (arr, pl) -> [arr] @ pl
    | Arith (t, c) -> (hstring_of_term t) @ [Hstring.make (string_of_int (value_c c))]

let hstring_of_op op =
  match op with
    | Eq -> [Hstring.make "="]
    | Lt -> [Hstring.make "<"]
    | Le -> [Hstring.make "<="]
    | Neq -> [Hstring.make "!="]
      
let rec hstring_of_atom a =
  match a with
    | True -> [Ast.htrue]
    | False -> [Ast.hfalse]
    | Comp (t1, op, t2) -> let ht1 = hstring_of_term t1 in
			   let hop = hstring_of_op op in
			   let ht2 = hstring_of_term t2 in
			   [Hstring.make "term"] @ ht1 @ hop @ [Hstring.make "term"] @ ht2
    | Ite (sa, a1, a2) -> let hsa = hstring_of_satom sa in
			  let ha1 = hstring_of_atom a1 in
			  let ha2 = hstring_of_atom a2 in
			  hsa @ ha1 @ ha2

and hstring_of_satom sa = SAtom.fold (fun a acc -> (hstring_of_atom a) @ h_new_line @ acc) sa []

let display_system () =
  Hashtbl.iter (
    fun id value -> 
      printf "%a@." (Hstring.print_list "\t") ([id]@(hstring_of_value value))
  ) htbl_globals;
  Hashtbl.iter (
    fun id array -> 
      printf "%a\t" Hstring.print id;
      Array.iteri (
	fun i el -> 
	  printf "%a " (Hstring.print_list " ") ([Hstring.make (string_of_int i)]@(hstring_of_value el))
      ) array;
      printf "@."
  ) htbl_arrays

let display_satom sa =
  printf " %a@." (Hstring.print_list " ") (hstring_of_satom sa)

let display_update ({up_arr; up_arg; up_swts}) =
  let hsw = ref [] in
  List.iter (fun (sa, t) -> let hsa = hstring_of_satom sa in
			    let ht = hstring_of_term t in
			    hsw := !hsw @ hsa @ ht
  ) up_swts;
  printf "Array : %a\n@." Hstring.print up_arr;
  printf "Args : %a\n@." (Hstring.print_list " ") up_arg;
  printf "Swts : %a\n@." (Hstring.print_list " ") (!hsw)

let display_transition trans =
  List.iter (
    fun {tr_name; tr_args; tr_reqs; tr_ureq; tr_assigns; tr_upds; tr_nondets} ->
      printf "-----------------------------\nName, args : %a\nReqs : @." (Hstring.print_list " ") ([tr_name]@tr_args);
      display_satom tr_reqs;
      
      printf "Ureqs : ";
      List.iter (
	fun (z, sa) ->
	  printf "%a " Hstring.print z;
	  List.iter display_satom sa
      ) tr_ureq;
      
      printf "\nAssigns : ";
      List.iter (
	fun (h, t) ->
	  printf "%a@." (Hstring.print_list " ") ([h]@hstring_of_term t)
      ) tr_assigns;

      printf "\nUpdate : ";
      List.iter display_update tr_upds;

      printf "\nNondets : %a\n-----------------------------@." (Hstring.print_list " ") tr_nondets
  ) trans
