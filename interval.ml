open Cubtypes

type up_bound = Term.Set.t

let empty_bound = Term.Set.empty

let equal_bound = Term.Set.equal

module Tmap = Map.Make (Term)

type quadvalue = Lower | Greater | Equal | Unknown
  
let order t1 t2 =
  match t1, t2 with

    | Elem (h1, _), Elem (h2, _) ->
      if Hstring.equal h1 h2 then Equal else Unknown

    | Elem (h1, _), Arith (Elem (h2, _), c) ->
      if Hstring.equal h1 h2 then
        let cs = const_sign c in
        begin
          match cs with
            | None -> Unknown
            | Some cs ->
              if cs < 0 then Greater else if cs = 0 then Equal else Lower
        end
      else Unknown

    | Arith (Elem (h1, _), c), Elem (h2, _) ->
      if Hstring.equal h1 h2 then
        let cs = const_sign c in
        begin
          match cs with
            | None -> Unknown
            | Some cs ->
              if cs < 0 then Lower else if cs = 0 then Equal else Greater
        end
      else Unknown

    | Access (h1, vl1), Access (h2, vl2) ->
      if Hstring.equal h1 h2 && Hstring.compare_list vl1 vl2 = 0
      then Equal else Unknown

    | Access (h1, vl1), Arith (Access (h2, vl2), c) ->
      if Hstring.equal h1 h2 && Hstring.compare_list vl1 vl2 = 0 then
        let cs = const_sign c in
        begin
          match cs with
            | None -> Unknown
            | Some cs ->
              if cs < 0 then Greater else if cs = 0 then Equal else Lower
        end
      else Unknown
        
    | Arith (Access (h1, vl1), c), Access (h2, vl2) ->
      if Hstring.equal h1 h2 && Hstring.compare_list vl1 vl2 = 0 then
        let cs = const_sign c in
        begin
          match cs with
            | None -> Unknown
            | Some cs ->
              if cs < 0 then Lower else if cs = 0 then Equal else Greater
        end
      else Unknown

    | _ -> Unknown

type swap = Replace of Term.t | Useless | Keep
      
let add_to_set t set =
  let res = Term.Set.fold (fun t2 acc ->
    match order t t2 with
      | Lower -> Replace t2
      | Greater -> Useless
      | Equal -> Useless
      | Unknown -> acc
  ) set Keep in
  match res with
    | Replace t2 -> Term.Set.add t (Term.Set.remove t2 set)
    | Useless -> set
    | Keep -> Term.Set.add t set
  
let assoc t1 op t2 map =
  let upb = try Tmap.find t1 map
    with Not_found -> empty_bound
  in
  let upb = match op with
    | Lt | Le -> add_to_set t2 upb
    | Eq | Neq -> assert false
  in Tmap.add t1 upb map
  
let rec associate t1 op t2 map =
  match t1 with
    | Elem _ | Access _ ->
      let map = assoc t1 op t2 map in
      begin
        match t2 with
          | Elem _ | Access _ ->
            assoc_transitivity t1 op t2 None map
              
          | Arith ((Elem _ | Access _) as t2, c) ->
            assoc_transitivity t1 op t2 (Some c) map

          | _ -> map
      end
        
    | Arith ((Elem _ | Access _) as t1, c) ->
      let oc = mult_const (-1) c in
      associate t1 op (Arith (t2, oc)) map
        
    | _ -> map

and assoc_transitivity t1 op t2 c map =
  let nset upb op =
    let set = match op with 
      | Lt | Le -> upb
      | Neq | Eq -> assert false
    in
    Term.Set.remove t1 (Term.Set.remove t2 set)
  in
  try
    let itvl = Tmap.find t2 map in
    let set = nset itvl op in
    Term.Set.fold (fun t map ->
      match c with
        | None -> associate t1 op t map
        | Some c -> associate t1 op (Arith (t, c)) map
    ) set map
  with Not_found -> map

let zero = MConst.singleton (ConstInt (Num.Int 0)) 0
    
let normalize_atom = function
  | Atom.Comp (((Elem _ | Access _) as t1), Le, ((Elem _ | Access _) as t2)) ->
    Atom.Comp (t1, Le, Arith (t2, zero))
  | a -> a
    
let normalize sa = sa
  (* SAtom.fold (fun a san -> SAtom.add (normalize_atom a) san) sa SAtom.empty *)
   
let map sa =
  let ineqs, untouched = SAtom.partition (
    function
      | Atom.Comp (t1, (Le | Lt), t2) -> true
      | _ -> false
  ) sa in
  let nineqs = normalize ineqs in
  Format.eprintf "Atoms : @[<v>%a@]@." SAtom.print nineqs;
  let rec mr map = 
    let m = SAtom.fold (fun a map ->
      match a with
        | Atom.Comp (t1, ((Le | Lt) as op), t2) ->
          associate t1 op t2 map
        | _ -> map
    ) nineqs map in
    if Tmap.equal equal_bound map m then m else mr m
  in mr Tmap.empty
    
let print fmt t =
  let p fmt t = Tmap.iter (fun te upb ->
    Format.fprintf fmt "@[%a <= %a@]@,"
      Term.print te Term.print_set upb
  ) t in
  Format.fprintf fmt "@[<v>%a@]" p t
