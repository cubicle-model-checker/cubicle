module Value = struct
  type t = string * int
  let compare (s1, i1) (s2, i2) =
    let c = compare s1 s2 in
    if c = 0 then compare i1 i2 else c
end

module type SMS = sig
    
  type t

  type state
  type value

  val new_state_machine : value list -> t

  val check : value list -> t -> bool
  val print : t -> unit

end

module SM : SMS with type value = Value.t = struct
    
  module State = struct
    type t = int 
    let compare = compare
  end
    
  type state = State.t
  type value = Value.t

  module SMap = Map.Make (State)
  module VMap = Map.Make (Value)

  type t = {
    init : state;
    final : state -> bool;
    smap : state VMap.t SMap.t;
  }

  let new_state_machine vl =
    let init = 0 in
    let gterm = List.length vl in
    let final s = s = gterm in
    let smap = 
      let c = ref 0 in
      List.fold_left (
        fun sm (s, i) ->
          let vm = VMap.singleton (s, i) (!c + 1) in
          let sm = SMap.add !c vm sm in
          incr c;
          sm
      ) SMap.empty vl in
    {init; final; smap}

  let rec check vl t =
    let rec cr st = function
      | [] -> t.final st
      | ((s, i) as v) :: vl -> 
        try
          let vm = SMap.find st t.smap in
          try let st' = VMap.find v vm in
              cr st' vl
          with Not_found -> false
        with Not_found -> false
    in cr t.init vl
      
  let print t = SMap.iter (
    fun st vm -> 
      Printf.printf "%d\n" st;
      VMap.iter (fun (s, i) st' ->
        Printf.printf "\t--%s, %d--> %d\n" s i st'
      ) vm
  ) t.smap
(* let transition = *)
end


let () =
  let r1 = ["t1", 1; "t2", 2] in
  let e1 = SM.new_state_machine r1 in
  Printf.printf "%b\n" (SM.check ["t1", 1; "t2", 2] e1);
  Printf.printf "%b\n" (SM.check ["t2", 1; "t1", 2] e1);
  SM.print e1

