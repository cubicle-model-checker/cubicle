open Why_ptree
open Smtlib2_ast
open Format
open Options


exception Not_Implemented

let num0 = Num.Int 0
let num10 = Num.Int 10
(* let num16 = Num.Int 16 *)

let decnumber s =
  let r = ref num0 in
  for i=0 to String.length s - 1 do
    r := Num.add_num (Num.mult_num num10 !r) 
      (Num.num_of_int (Char.code s.[i] - Char.code '0'))
  done;
  !r

(* let hexnumber s = *)
(*   let r = ref num0 in *)
(*   for i=0 to String.length s - 1 do *)
(*     let c = s.[i] in *)
(*     let v =  *)
(*       match c with *)
(* 	| '0'..'9' -> Char.code c - Char.code '0' *)
(* 	| 'a'..'f' -> Char.code c - Char.code 'a' + 10 *)
(* 	| 'A'..'F' -> Char.code c - Char.code 'A' + 10 *)
(* 	| _ -> assert false *)
(*     in *)
(*     r := Num.add_num (Num.mult_num num16 !r) (Num.num_of_int v) *)
(*   done; *)
(*     !r *)

module M = Map.Make(String)

module MString = 
  Map.Make(struct type t = string let compare = Pervasives.compare end)

module S = Set.Make(String)

let predicates = S.empty

let const_of_specconstant = function 
  | SpecConstString (_, s) -> assert false
  (* | SpecConstString (_, "true") -> ConstTrue *)
  (* | SpecConstString (_, "false") -> ConstFalse *)
  | SpecConstsDec (_, s) -> ConstReal (decnumber s)
  | SpecConstNum (_, s) -> ConstInt s
  | SpecConstsHex (_, s) 
  | SpecConstsBinary (_, s) -> 
    ConstInt (Scanf.sscanf s "%i" (Printf.sprintf "%d"))

let string_of_symbol = function
  | Symbol (pos, s) 
  | SymbolWithOr (pos, s) -> s

let stringi_of_identifier = function
  | IdSymbol (_, sy) -> string_of_symbol sy, None
  | IdUnderscoreSymNum (_, sy, (_, sl)) -> 
    if List.length sl <> 1 then raise Not_Implemented
    else Scanf.sscanf (List.hd sl) "%d" 
      (fun n -> string_of_symbol sy, Some n)

let rec ppure_type_of_sort = function
  | SortIdentifier (pos, id) ->
    begin 
      match stringi_of_identifier id with 
	| "Int", _ -> PPTint
	| "Bool", _ -> PPTbool
	| "Real", _ -> PPTreal
	| "Bitv", Some n -> PPTbitv n
	| s, _ -> PPTexternal ([], s, pos)
    end
  | SortIdSortMulti (pos, id, (_, sortlist)) ->
    begin 
      match stringi_of_identifier id with 
	| "Array", _ ->
	  if List.length sortlist <> 2 then raise Not_Implemented
	  else 
	    let pptl = List.map ppure_type_of_sort sortlist in
	    (match pptl with 
	      | [] | [_] -> raise Not_Implemented
	      | [p1; p2] ->
		(* if p1 = PPTint then PPTfarray p2 *)
		(* else *) PPTexternal (pptl, "farray", pos)
	      | _ -> raise Not_Implemented)
	| s, _ -> 
	  let pptl = List.map ppure_type_of_sort sortlist in
	  PPTexternal (pptl, s, pos)
    end
    
let stringi_of_qualidentifier = function
  | QualIdentifierId (_, id)
  | QualIdentifierAs (_, id, _) -> stringi_of_identifier id

let stringppt_of_sortedvar = function 
  | SortedVarSymSort (_, sy, so) -> 
    string_of_symbol sy, ppure_type_of_sort so

let infix_of_string = function
  | "=" -> Some PPeq
  | "<=>" -> Some PPiff
  | "<" -> Some PPlt
  | "<=" -> Some PPle
  | ">" -> Some PPgt
  | ">=" -> Some PPge
  | "+" -> Some PPadd
  | "-" -> Some PPsub
  | "*" -> Some PPmul
  | "/" | "div" -> Some PPdiv
  | "%" | "mod" -> Some PPmod
  | "and" -> Some PPand
  | "or" -> Some PPor
  | "=>" | "implies" -> Some PPimplies
  | _ -> None


let prefix_of_string = function
  | "not" -> Some PPnot
  | _ -> None


let rec inline_lexpr s leb excl { pp_loc = pos; pp_desc = descv } =
  { pp_loc = pos; pp_desc = inline_ppdesc s leb excl descv }

and inline_ppdesc s ({ pp_desc = descb } as leb) excl = function
  | PPvar s' when not (List.mem s excl) && s' = s -> descb
  | PPapp (s', ll) ->
    PPapp (s', List.map (inline_lexpr s leb excl) ll)
  | PPconst c -> PPconst c
  | PPinfix (le1, i, le2) ->
    PPinfix (inline_lexpr s leb excl le1, i, inline_lexpr s leb excl le2)
  | PPprefix (pre, le) ->
    PPprefix (pre, inline_lexpr s leb excl le)
  | PPget (le1, le2) ->
    PPget (inline_lexpr s leb excl le1, inline_lexpr s leb excl le2)
  | PPset (le1, le2, le3) ->
    PPset (inline_lexpr s leb excl le1, 
	   inline_lexpr s leb excl le2, 
	   inline_lexpr s leb excl le3)
  | PPextract (le1, le2, le3) ->
    PPextract (inline_lexpr s leb excl le1, 
	       inline_lexpr s leb excl le2, 
	       inline_lexpr s leb excl le3)
  | PPconcat(le1, le2) ->
    PPconcat (inline_lexpr s leb excl le1, inline_lexpr s leb excl le2)
  | PPif(le1, le2, le3) ->
    PPif (inline_lexpr s leb excl le1, 
	  inline_lexpr s leb excl le2, 
	  inline_lexpr s leb excl le3)
  | PPforall (sl, pt, lll, le) ->
    let excl = sl@excl in
    PPforall (sl, pt, List.map (List.map (inline_lexpr s leb excl)) lll,
	      inline_lexpr s leb excl le)
  | PPexists (sl, pt, le) ->
    let excl = sl@excl in
    PPexists (sl, pt, inline_lexpr s leb excl le)
  | PPnamed (n, le) ->
    PPnamed (n, inline_lexpr s leb excl le)
  | PPlet (n, le1, le2) ->
    PPlet (n, inline_lexpr s leb excl le1, inline_lexpr s leb excl le2)
  | desc -> desc
 

let rec is_prop predicates excl { pp_desc = descv } =
  match descv with
    | PPvar s -> not (List.mem s excl) && S.mem s predicates
    | PPapp (s, _) -> not (List.mem s excl) && S.mem s predicates
    | PPconst _ -> false
    | PPinfix (_, (PPeq | PPle | PPlt | PPge | PPgt | PPneq 
		      | PPand | PPor | PPimplies | PPiff), _) -> true
    | PPprefix (PPnot, _) -> true
    | PPget _ | PPset _ | PPextract _ | PPconcat _ -> false
    | PPif (_, l, _) -> is_prop predicates excl l
    | PPforall _ | PPexists _ -> true
    | PPnamed (_, l) -> is_prop predicates excl l
    | PPlet (s, _, l) -> is_prop predicates (s::excl) l
    | _ -> false


let rec stringlexpr_of_varbinding predicates = function
  | VarBindingSymTerm (_, sy, t) -> 
    string_of_symbol sy, lexpr_of_term predicates t

and ppdesc_of_sexpr = function
  | SexprSpecConst (pos, sc) -> PPconst (const_of_specconstant sc) 
  | SexprSymbol (pos, sy) -> ppconstvar_of_string (string_of_symbol sy) 
  | SexprInParen (pos, (_, (SexprSymbol (_, sy))::sel)) ->
    let s = string_of_symbol sy in
    (match prefix_of_string s with
      | Some x -> 
	if List.length sel <> 1 then raise Not_Implemented
	else PPprefix (x, lexpr_of_sexpr (List.hd sel))
      | None ->
	(match infix_of_string s with
	  | Some x -> ppinfix_sexprlist pos x sel
	  | None -> 
	    (match s with
	      | "select" -> 
		PPget ((lexpr_of_sexpr (List.nth sel 0)),
		       (lexpr_of_sexpr (List.nth sel 1)))
	      | "store" -> 
		PPset ((lexpr_of_sexpr (List.nth sel 0)),
		       (lexpr_of_sexpr (List.nth sel 1)),
		       (lexpr_of_sexpr (List.nth sel 2)))
	      | "ite" -> 
		PPif ((lexpr_of_sexpr (List.nth sel 0)),
		      (lexpr_of_sexpr (List.nth sel 1)),
		      (lexpr_of_sexpr (List.nth sel 2)))
	      | "distinct" ->
		PPdistinct (List.map lexpr_of_sexpr sel)
	      | _ ->
		PPapp (s, List.map lexpr_of_sexpr sel)
	    )
	)
    )
  | _ -> assert false

and lexpr_of_sexpr se = match se with 
  | SexprSpecConst (pos, _) 
  | SexprSymbol (pos, _) 
  | SexprInParen (pos, (_, _)) -> 
    { pp_loc = pos; pp_desc = ppdesc_of_sexpr se }
  | _ -> assert false

and triggers_of_attributelist = function
  | [] -> []
  | (AttributeKeywordValue (_, ":pattern", 
			    (AttributeValSexpr (pos, (_, sel)))))::atl ->
    (List.map lexpr_of_sexpr sel)::(triggers_of_attributelist atl)
  | _::atl -> triggers_of_attributelist atl


and ppinfix_alist predicates pos ppi tl tfunc =
  (* let tl = if ppi = PPneq && List.length tl >= 3 then tl@[List.hd tl] else tl in *)
  let rec aux predicates pos ppi = function
    | [] -> Loc.report pos; raise Not_Implemented
    | [a] -> 
      if ppi = PPsub then PPprefix (PPneg, (tfunc a))
      else raise Not_Implemented
    | [a;b] -> 
      let la = tfunc a in
      let lb = tfunc b in
      let are_prop = is_prop predicates [] la || is_prop predicates [] lb in
      let ppi, negate = 
	(match ppi with 
	  | PPeq when are_prop -> PPiff, false
	  | PPneq when are_prop -> PPiff, true
	  | _ -> ppi, false) in
      if negate then 
	PPprefix (PPnot, { pp_loc = pos; pp_desc = PPinfix (la, ppi, lb) })
      else PPinfix (la, ppi, lb)
    | a::(b::_ as l) -> 
      let la = tfunc a in
      let are_prop = is_prop predicates [] la in
      let ppi = 
	(match ppi with 
	  | PPeq when are_prop -> PPiff
	  | _ -> ppi) in 
      let le = { pp_loc = pos; pp_desc = aux predicates pos ppi l }
      in
      if ppi = PPneq then
	let lb = tfunc b in
	let n1 = { pp_loc = pos; pp_desc = PPinfix (la, ppi, lb) } in
	PPinfix (n1, PPand, le)
      else 
	PPinfix (la, ppi, le)
  in aux predicates pos ppi tl

and ppinfix_termlist pre pos ppi tl = 
  ppinfix_alist pre pos ppi tl (lexpr_of_term pre)


and ppinfix_blist predicates pos ppi tl tfunc = 
  (* FIXME = ppinfix_alist predicates pos ppi tl tfunc *)
  (* let tl = if ppi = PPneq && List.length tl >= 3 then tl@[List.hd tl] else tl in *)
  let rec aux predicates pos ppi = function
    | [] -> Loc.report pos; raise Not_Implemented
    | [a] -> 
      if ppi = PPsub then PPprefix (PPneg, (tfunc a))
      else raise Not_Implemented
    | [a;b] -> 
      let la = tfunc a in
      let lb = tfunc b in
      let are_prop = is_prop predicates [] la || is_prop predicates [] lb in
      let ppi, negate = 
	(match ppi with 
	  | PPeq when are_prop -> PPiff, false
	  | PPneq when are_prop -> PPiff, true
	  | _ -> ppi, false) in
      if negate then 
	PPprefix (PPnot, { pp_loc = pos; pp_desc = PPinfix (la, ppi, lb) })
      else PPinfix (la, ppi, lb)
    | a::(b::_ as l) -> 
      let la = tfunc a in
      let are_prop = is_prop predicates [] la in
      let ppi = 
	(match ppi with 
	  | PPeq when are_prop -> PPiff
	  | _ -> ppi) in 
      let le = { pp_loc = pos; pp_desc = aux predicates pos ppi l }
      in
      if ppi = PPneq then
	let lb = tfunc b in
	let n1 = { pp_loc = pos; pp_desc = PPinfix (la, ppi, lb) } in
	PPinfix (n1, PPand, le)
      else 
	PPinfix (la, ppi, le)
  in aux predicates pos ppi tl

and ppinfix_sexprlist pos ppi sel = 
  ppinfix_blist S.empty pos ppi sel lexpr_of_sexpr


and let_of_varbindinglist predicates pos t = function
  | [] -> raise Not_Implemented
  | [vb] -> 
    let (s, le) = stringlexpr_of_varbinding predicates vb in
    let are_prop = is_prop predicates [] le in
    let predicates = if are_prop then (S.add s predicates) else predicates in
    if (* true ||  *)are_prop then 
      let { pp_desc = ppd } = 
	inline_lexpr s le [] (lexpr_of_term predicates t) in
      ppd
    else PPlet (s, le, lexpr_of_term predicates t)
  | vb::l -> 
    let (s, le) = stringlexpr_of_varbinding predicates vb in
    let are_prop = is_prop predicates [] le in
    let predicates = if are_prop then (S.add s predicates) else predicates in
    let le2 = 
      { pp_loc = pos; pp_desc = let_of_varbindinglist predicates pos t l } in
    if (* true ||  *)are_prop then
      let { pp_desc = ppd } = inline_lexpr s le [] le2 in
      ppd
    else PPlet (s, le, le2)

and forall_of_sortedvarlist pos t triggers = function
  | [] -> raise Not_Implemented
  | [sv] -> 
    let (s, ppt) = stringppt_of_sortedvar sv in
    PPforall ([s], ppt, triggers, lexpr_of_term predicates t)
  | sv::l -> 
    let (s, ppt) = stringppt_of_sortedvar sv in
    let le2 = { pp_loc = pos; 
		pp_desc = forall_of_sortedvarlist pos t triggers l } 
    in
    PPforall ([s], ppt, [], le2)

and exists_of_sortedvarlist pos t = function
  | [] -> raise Not_Implemented
  | [sv] -> 
    let (s, ppt) = stringppt_of_sortedvar sv in
    PPexists ([s], ppt, lexpr_of_term predicates t)
  | sv::l -> 
    let (s, ppt) = stringppt_of_sortedvar sv in
    let le2 = { pp_loc = pos; pp_desc = exists_of_sortedvarlist pos t l } in
    PPexists ([s], ppt, le2)

and ppapp_of_string pos s tl predicates =
  match prefix_of_string s with
    | Some x -> 
      if List.length tl <> 1 then raise Not_Implemented
      else PPprefix (x, lexpr_of_term predicates (List.hd tl))
    | None -> 
      (match infix_of_string s with
	| Some x -> 
	  ppinfix_termlist predicates pos x tl
	| None ->
	  (match s with
	    | "select" -> 
	      PPget ((lexpr_of_term predicates (List.nth tl 0)),
		     (lexpr_of_term predicates (List.nth tl 1)))
	    | "store" -> 
	      PPset ((lexpr_of_term predicates (List.nth tl 0)),
		     (lexpr_of_term predicates (List.nth tl 1)),
		     (lexpr_of_term predicates (List.nth tl 2)))
	    | "ite" -> 
	      PPif ((lexpr_of_term predicates (List.nth tl 0)),
		    (lexpr_of_term predicates (List.nth tl 1)),
		    (lexpr_of_term predicates (List.nth tl 2)))
	    | "distinct" ->
	      PPdistinct (List.map (lexpr_of_term predicates) tl)
	    | _ ->
	      PPapp (s, List.map (lexpr_of_term predicates) tl)
	  )
      )

and ppconstvar_of_string = function
  | "true" -> PPconst ConstTrue
  | "false" -> PPconst ConstFalse
  | s -> PPvar s

and ppdesc_of_term predicates = function
  | TermSpecConst (_,sc) -> PPconst (const_of_specconstant sc)
  | TermQualIdentifier (_, qi) -> 
    let s = fst (stringi_of_qualidentifier qi) in
    ppconstvar_of_string s
  | TermQualIdTerm (pos, qi, (_, tl)) -> 
    let s = fst (stringi_of_qualidentifier qi) in
    ppapp_of_string pos s tl predicates
    (*match prefix_of_string s with
      | Some x -> 
	if List.length tl <> 1 then raise Not_Implemented
	else PPprefix (x, lexpr_of_term predicates (List.hd tl))
      | None -> 
	(match infix_of_string s with
	  | Some x -> ppinfix_termlist predicates pos x tl
	  | None ->
	    (match s with
	      | "select" -> 
		PPget ((lexpr_of_term predicates (List.nth tl 0)),
		       (lexpr_of_term predicates (List.nth tl 1)))
	      | "store" -> 
		PPset ((lexpr_of_term predicates (List.nth tl 0)),
		       (lexpr_of_term predicates (List.nth tl 1)),
		       (lexpr_of_term predicates (List.nth tl 2)))
	      | _ ->
		PPapp (s, List.map (lexpr_of_term predicates) tl)
	    )
	)
    *)
  | TermLetTerm (pos, (_, vbl), t) -> 
    let_of_varbindinglist predicates pos t vbl
  
(* FIXME : out of scope bounded variables inside triggers ! 
  | TermForAllTerm (pos, (_, svl),  TermExclimationPt (_, t, (_, atl))) ->
    forall_of_sortedvarlist pos t (triggers_of_attributelist atl) svl
*)
  | TermForAllTerm (pos, (_, svl), t) ->
    forall_of_sortedvarlist pos t [] svl
  | TermExistsTerm (pos, (_, svl), t) ->
    exists_of_sortedvarlist pos t svl
  | TermExclimationPt (_, t, _) -> ppdesc_of_term predicates t

and lexpr_of_term predicates t = match t with
  | TermSpecConst (pos, _)
  | TermQualIdentifier (pos, _) 
  | TermQualIdTerm (pos, _, _)
  | TermLetTerm (pos, _, _) 
  | TermForAllTerm (pos, _, _)
  | TermExistsTerm (pos, _, _)
  | TermExclimationPt (pos, _, _) ->
    { pp_loc = pos;
      pp_desc = ppdesc_of_term predicates t }

let rec last_axiom_to_goal pos acc = function
  | [] -> 
    let true_lexpr = { pp_loc = pos; pp_desc = PPconst ConstTrue } in
    (Goal (pos, "", true_lexpr))::(List.rev acc)
  | (Axiom (pos', n, a))::r ->
    (Axiom (pos', n, a))::(Goal (pos, n, a))::(List.rev_append acc r)
  | d::r -> last_axiom_to_goal pos (d::acc) r

let decls_of_command (acc, predicates) = function
  | CSetLogic _
  | CSetOption _
  | CSetInfo _ -> acc, predicates
  | CDeclareSort (pos, sy, n) ->
    let n = Scanf.sscanf n "%d" (fun x -> x) in
    let rec make_vt = function
      | nb when nb = n -> []
      | nb -> (Printf.sprintf "\'a%d" nb)::(make_vt (nb + 1)) in
    (TypeDecl (pos, make_vt n, string_of_symbol sy, Abstract))::acc, predicates
  | CDefineSort (pos, sy, (_, syl), so) -> assert false
  | CDeclareFun (pos, sy, (_, sol), so) ->
    let ppt = ppure_type_of_sort so in
    let logic_type = 
      let pptl = List.map ppure_type_of_sort sol in
      if ppt = PPTbool then PPredicate pptl
      else PFunction (pptl, ppt)
    in
    let s = string_of_symbol sy in
    let predicates = if ppt = PPTbool then S.add s predicates else predicates in
    (Logic (pos, Symbols.Other, [s], logic_type))::acc, predicates
  | CDefineFun (pos, sy, (pos2, svl), so, t) ->
    let spl = List.map (fun sv -> 
      let s, ppt = stringppt_of_sortedvar sv in
      pos2, s, ppt) svl in
    let s = string_of_symbol sy in
    let ppt = ppure_type_of_sort so in
    let le = lexpr_of_term predicates t in
    if ppt = PPTbool then 
      (Predicate_def (pos, s, spl, le))::acc, S.add s predicates
    else (Function_def (pos, s, spl, ppt, le))::acc, predicates
  | CAssert (pos, t) ->
    (Axiom (pos, "", lexpr_of_term predicates t))::acc, predicates
  | CCheckSat pos -> 
    (*let true_lexpr = { pp_loc = pos; pp_desc = PPconst ConstTrue } in
    (Goal (pos, "check-sat", true_lexpr))::*)
    last_axiom_to_goal pos [] acc, predicates
  | CPush _
  | CPop _
  | CGetAssert _
  | CGetProof _
  | CGetUnsatCore _
  | CGetValue _
  | CGetAssign _
  | CGetOption _
  | CGetInfo _
  | CExit _ -> acc, predicates


let smt2_to_why = function
  | Some (Commands (_, (pos, cl))) ->
    List.rev (fst (List.fold_left decls_of_command ([], predicates) cl))
  | None -> []
