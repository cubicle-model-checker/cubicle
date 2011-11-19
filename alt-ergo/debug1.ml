open Solver_types

open Format
let fmt = err_formatter
  
let d = false
let d_decisions = false
let d_model = false
let d_trail = false
let minisat_like_pp = true

let sep = "------------------------------------------------"
  
let sign a = if a==a.var.pa then "" else "-"
  
let level a =
  match a.var.level, a.var.reason with 
    | n, _ when n < 0 -> assert false
    | 0, Some c -> sprintf "->0/%s" c.name
    | 0, None   -> "@0"
    | n, Some c -> sprintf "->%d/%s" n c.name
    | n, None   -> sprintf "@@%d" n

let value a = 
  if a.is_true then sprintf "[T%s]" (level a)
  else if a.neg.is_true then sprintf "[F%s]" (level a)
  else ""

let value_ms_like a = 
  if a.is_true then sprintf ":1%s" (level a)
  else if a.neg.is_true then sprintf ":0%s" (level a)
  else ":X"

let atom fmt a = 
  if minisat_like_pp then
    fprintf fmt "%s%d%s [lit:%a]" 
      (sign a) (a.var.vid+1) (value_ms_like a) Literal.LT.print a.lit
  else
    fprintf fmt "%s%d%s [lit:%a]" 
      (sign a) (a.var.vid+1) (value a) Literal.LT.print a.lit


let atoms_list fmt l = List.iter (fprintf fmt "%a ; " atom) l
let atoms_array fmt arr = Array.iter (fprintf fmt "%a ; " atom) arr

let atoms_vec fmt vec = 
  for i = 0 to Vec.size vec - 1 do
    fprintf fmt "%a ; " atom (Vec.get vec i)
  done

let clause fmt {name=name; atoms=arr} =
  fprintf fmt "%s:{ %a}" name atoms_vec arr

let clause2 fmt {name=name; atoms=arr; learnt=learnt; removed=removed} =
  fprintf fmt "%s:%s{ %a}" 
    (if learnt then "L" else "C") 
    (if removed then "removed" else "")
    atoms_vec arr
    
let clause_list fmt cl = List.iter (fprintf fmt "%a  , " clause2) cl

let add_clause cl = 
  if d_decisions then begin
    fprintf fmt "I add a clause: %a@." clause2 cl;
    fprintf fmt "with the watch literals %a  and  %a@.@."
      atom (Vec.get cl.atoms 0).neg 
      atom (Vec.get cl.atoms 1).neg
  end

let add_unit_clause a = 
  if d then fprintf fmt "I DON'T add the unit clause: %a@." atom a
    
let enqueue a = 
  if d_decisions then fprintf fmt "I enqueue the atom %a@." atom a

let propagate a = 
  if d_decisions then fprintf fmt "I propagate the atom %a@." atom a

let theory_propagate a = 
  if d_decisions then fprintf fmt "I theory-propagate the atom %a@." atom a

let propagate_unit_clause cl = 
  if d_decisions then fprintf fmt "The clause %a becomes unit@." clause cl

let propagate_false_clause cl = 
  if d_decisions then fprintf fmt "The clause %a becomes FALSE@." clause cl

let propagate_true_clause cl = 
  if d_decisions then fprintf fmt "The clause %a becomes TRUE@." clause cl

let watched_of_a a =
  let ws = a.watched in
  if false && d_decisions then begin
    fprintf fmt "%a watches the following clauses:@." atom a;
    for i = 0 to Vec.size ws -1 do
      fprintf fmt " >%a@." clause2 (Vec.get ws i)
    done
  end

let trail_content trail =
  if d_trail then begin
    fprintf fmt "The trail contrains:@.";
    for i = Vec.size trail - 1 downto 0 do
      fprintf fmt "  | %a@." atom (Vec.get trail i);
    done;
    fprintf fmt "  --------------@."
  end

let decide decisions lvl v =
  if d_decisions then 
    fprintf fmt "(%dth) I decide the atom %a at level %d@." 
      decisions atom v lvl
      
let boolean_conflict c_level conflict_cpt =
  if d_decisions then 
    fprintf fmt "I have a (%d-th) boolean conflict at level %d@." 
      !conflict_cpt c_level

let theory_conflict c_level conflict_cpt =
  if d_decisions then 
    fprintf fmt "I have a (%d-th) theory conflict at level %d@." 
      !conflict_cpt c_level

let analyze_conflict blevel learnt = 
  if d_decisions then 
    fprintf fmt "Backjump to level %d and learn the clause { %a}@." 
      blevel atoms_list learnt

let print_model vec = 
  if d_model then begin
    fprintf fmt "MODEL: @.";
    for i = 0 to Vec.size vec - 1 do 
      let v = Vec.get vec i in
      fprintf fmt "%a@." atom v.pa;
      assert (v.pa.is_true || v.na.is_true)
    done
  end  
