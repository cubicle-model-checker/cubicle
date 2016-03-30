module type OrderedChar = sig
  type t
  val compare : t -> t -> int
  val end_char : t
  val fprint : Format.formatter -> t -> unit
  val fprint_dot : Format.formatter -> t -> unit
end

module type ICS = sig
    
  type c
  type t =  c * int
      
  val from_char : c -> t
  val end_char : t
  val compare : t -> t -> int
  val fprint : Format.formatter -> t -> unit
  val fprint_dot : Format.formatter -> t -> unit

end

module Make_IC (C : OrderedChar) : ICS with type c = C.t = struct

  type c = C.t

  type t = c * int

  let from_char =
    let ht = Hashtbl.create 17 in
    fun v -> 
      let c = 
        try
          let c = (Hashtbl.find ht v) + 1 in
          Hashtbl.replace ht v c;
          c
        with Not_found -> 
          Hashtbl.add ht v 1;
          1
      in (v, c)

  let end_char = C.end_char, -1

  let compare (v1, i1) (v2, i2) = 
    let c = C.compare v1 v2 in
    if c = 0 then compare i1 i2 else c

  let fprint fmt (v, i) = Format.fprintf fmt "%a[%d]" C.fprint v i

  let fprint_dot fmt ((c, i) as ic) =
    if ic = end_char then Format.fprintf fmt "# "
    else Format.fprintf fmt "%a%d " C.fprint_dot c i

end

module type RES = sig

  module C : OrderedChar
  module ICSet : Set.S with type elt = C.t * int

  type simple_r = 
    | SEpsilon 
    | SChar of C.t 
    | SUnion of simple_r list
    | SConcat of simple_r list
    | SStar of simple_r
    | SPlus of simple_r
    | SOption of simple_r

  type ts = simple_r (* {from_start : bool; simple_r : simple_r} *)

  type ichar

  type r = 
    | Epsilon
    | IChar of ichar
    | Union of r list
    | Concat of r list
    | Star of r
    | Plus of r
    | Option of r

  type t = r (* {from_start : bool; r : r} *)

  val new_t : ts -> t
  val from_list : ts list -> t

  val null : t -> bool

  val first : t -> ICSet.t
  val last : t -> ICSet.t
  val follow : ichar -> t -> ICSet.t

  val next_state : t -> ICSet.t -> C.t -> ICSet.t

  val add_eof : t -> t

  val print_set : ICSet.t -> unit
  val fprint_set_dot : Format.formatter -> ICSet.t -> unit

  val fprint : Format.formatter -> t -> unit
end

module Make_Regexp (C : OrderedChar) : RES with module C = C = struct
      
    module C = C
    module IC = Make_IC(C)

    module ICSet = Set.Make (IC)

    type char = C.t

    type simple_r = 
      | SEpsilon 
      | SChar of char 
      | SUnion of simple_r list
      | SConcat of simple_r list
      | SStar of simple_r
      | SPlus of simple_r
      | SOption of simple_r

    type ts = simple_r (* {sfrom_start : bool; simple_r : simple_r} *)

    type ichar = IC.t

    let from_char = IC.from_char

    type r = 
      | Epsilon
      | IChar of ichar
      | Union of r list
      | Concat of r list
      | Star of r
      | Plus of r
      | Option of r

    type t = r
    let new_t s = 
      let rec nr = function
        | SEpsilon -> Epsilon
        | SChar c -> IChar (IC.from_char c)
        | SUnion tl -> Union (List.map nr tl)
        | SConcat tl -> Concat (List.map nr tl)
        | SStar t -> Star (nr t)
        | SPlus t -> Plus (nr t)
        | SOption t -> Option (nr t)
      in (* {from_start = s.sfrom_start; r =  *)nr s

    let from_list t = match t with
      | [e] -> new_t e
      | _ -> Union (List.map new_t t)

    let fprint_set fmt s =
      ICSet.iter (fun v -> Format.fprintf fmt "%a " IC.fprint v) s

    let pp_sep_un fmt () = Format.fprintf fmt "|"
    let pp_sep_not _ () = ()

    let rec fprint fmt = function
      | Epsilon -> ()
      | IChar (c, i) -> Format.fprintf fmt "%a" C.fprint c
      | Union tl -> Format.fprintf fmt "[%a]" 
        (Format.pp_print_list ~pp_sep:pp_sep_un fprint) tl
      | Concat tl -> Format.fprintf fmt "(%a)" 
        (Format.pp_print_list ~pp_sep:pp_sep_not fprint) tl
      | Star t -> Format.fprintf fmt "\\%a/*" fprint t
      | Plus t -> Format.fprintf fmt "\\%a/+" fprint t
      | Option t -> Format.fprintf fmt "{%a}?" fprint t

    let rec null = function
      | Epsilon | Star _ | Option _ -> true
      | IChar _ -> false
      | Union tl -> List.exists null tl
      | Concat tl -> List.for_all null tl
      | Plus t -> null t


    let first t =
      let rec fconcat acc = function
        | [] -> acc
        | t :: tl -> let ft = fr acc t in
                     if null t then fconcat ft tl
                     else ft
                       
      and fr acc = function
        | Epsilon -> acc
        | IChar iv -> ICSet.add iv acc
        | Union tl -> List.fold_left fr acc tl
        | Concat tl -> fconcat acc tl
        | Star t | Option t | Plus t -> fr acc t
      in
      fr ICSet.empty t
        
    let last t =
      let rec lconcat acc = function
        | [] -> acc
        | t :: tl -> let lt = lr acc t in
                     if null t then lconcat lt tl
                     else lt
      and lr acc = function
        | Epsilon -> acc
        | IChar iv -> ICSet.add iv acc
        | Union tl -> List.fold_left lr acc tl
        | Concat tl -> lconcat acc (List.rev tl)
        | Star t | Option t | Plus t -> lr acc t
      in
      lr ICSet.empty t

    let follow c t =
      let rec fconcat acc = function
        | r1 :: ((r2 :: _) as rtl) ->
          let s = fr acc r2  in
          let acc = if ICSet.mem c (last r1) 
            then ICSet.union s (first (Concat rtl)) else s in
          fconcat acc rtl
        | [] | [_] -> acc
      and fr acc = function
        | Epsilon | IChar _ -> acc
        | Union tl -> List.fold_left fr acc tl
        | Concat tl -> fconcat (fr acc (List.hd tl)) tl
        | Star t | Plus t -> 
          let s = fr acc t in
          if ICSet.mem c (last t) then ICSet.union s (first t) else s
        | Option t -> fr acc t
      in
      fr ICSet.empty t

    let next_state r st c =
      ICSet.fold (
        fun ((c', _) as ic) st' ->
          if c' = c then 
            ICSet.union st' (follow ic r) else st'
      ) st ICSet.empty

    let add_eof r = Concat [r; IChar IC.end_char]

    let print_set s =
      ICSet.iter (fun v -> Format.printf "%a\n" IC.fprint v) s

    let fprint_set_dot fmt s =
      ICSet.iter (fun v -> Format.fprintf fmt "%a\n" IC.fprint_dot v) s

        
  end
         
module type AS = sig

  type regexp
  type state

  type char
    
  type t

  val make_automaton : regexp -> t

  val recognize : t -> char list -> bool

  val save_automaton : string -> t -> unit
end


module Make_Automaton (R : RES) : AS 
  with type regexp = R.t and type char = R.C.t = struct
    
  module SMap = Map.Make (R.ICSet)
  module CMap = Map.Make (R.C)

  module IC = Make_IC(R.C)

  type regexp = R.t
  type state = R.ICSet.t

  type char = R.C.t

  type t = {
    init : state;
    trans : state CMap.t SMap.t;
  }

  let make_automaton r =
    let r = R.add_eof r in
    let init = R.first r in
    let trans = ref SMap.empty in
    let rec transitions q =
      if not (SMap.mem q !trans) then begin
        trans := SMap.add q CMap.empty !trans;
        R.ICSet.iter
          (fun (c,_) ->
            let t = SMap.find q !trans in
            if not (CMap.mem c t) then begin
              let q' = R.next_state r q c in
              trans := SMap.add q (CMap.add c q' t) !trans;
              transitions q'
            end)
          q
      end
    in
    transitions init;
    {init; trans = !trans}

  let terminal st = R.ICSet.mem IC.end_char st


  let recognize_start t cl =
    let rec rl st = function
      | [] -> terminal st
      | hd :: tl -> let tr = SMap.find st t.trans in
                    let st' = CMap.find hd tr in
                    rl st' tl
    in
    try rl t.init cl with Not_found -> false
      
  let recognize_anywhere t cl =
    let rec rl st = function
      | [] -> terminal st
      | hd :: tl -> 
        try
          let tr = SMap.find st t.trans in
          let st' = CMap.find hd tr in
          rl st' tl
        with Not_found -> rl t.init tl
    in
    rl t.init cl
    
  let recognize t cl = 
    (* if t.from_start then recognize_start t cl *)
    (* else *) recognize_anywhere t cl

  let fprint_state_dot fmt q = R.fprint_set_dot fmt q

  let fprint_transition_dot fmt q c q' =
    Format.fprintf fmt "\"%a\" -> \"%a\" [label=\"%a\"];@\n"
      fprint_state_dot q
      fprint_state_dot q'
      R.C.fprint_dot c

  let fprint_automaton_dot fmt a =
    Format.fprintf fmt "digraph A {@\n";
    Format.fprintf fmt "  @[\"%a\" [ shape = \"rect\"];@\n" 
      fprint_state_dot a.init;
    SMap.iter
      (fun q t -> CMap.iter (fun c q' -> fprint_transition_dot fmt q c q') t)
      a.trans;
    Format.fprintf fmt "@]@\n}@."

  let save_automaton file a =
    let ch = open_out file in
    Format.fprintf (Format.formatter_of_out_channel ch) 
      "%a" fprint_automaton_dot a;
    close_out ch;
    match Sys.command ("dot -Tpdf "^file^".dot > "^file^".pdf") with
      | 0 -> ()
      | _ -> Format.eprintf 
        "There was an error with dot. Make sure graphviz is installed."

end

type tr = Hstring.t * Hstring.t list

module Trans : OrderedChar with type t = tr = struct 

  type t = tr
  let end_char = Hstring.make "dummy_trans", [Hstring.make "#-1"]
  
  let compare = compare

  let pp_sep_un fmt () = Format.fprintf fmt ", "

  let fprint fmt (name, vars) = Format.fprintf fmt "%a(%a)" Hstring.print name
    (Format.pp_print_list ~pp_sep:pp_sep_un Hstring.print) vars
    
  let fprint_dot = fprint

end

module RTrans : RES with type C.t = tr = Make_Regexp(Trans)
module Automaton : AS
  with type regexp = RTrans.t and type char = RTrans.C.t = Make_Automaton(RTrans)

