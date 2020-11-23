open Format
open Options
open Util
open Ast
open Types


module T = Smt.Term
module F = Smt.Formula

module SMT = Smt.Make (Options)


let make_op_comp = function
  | Eq -> F.Eq
  | Lt -> F.Lt
  | Le -> F.Le
  | Neq -> F.Neq

let make_const = function
  | ConstInt i -> T.make_int i
  | ConstReal i -> T.make_real i
  | ConstName n -> T.make_app n []

let ty_const = function
  | ConstInt _ -> Smt.Type.type_int
  | ConstReal _ -> Smt.Type.type_real
  | ConstName n -> snd (Smt.Symbol.type_of n)

let rec mult_const tc c i =
 match i with
  | 0 -> 
    if ty_const c = Smt.Type.type_int then T.make_int (Num.Int 0)
    else T.make_real (Num.Int 0)
  | 1 -> tc
  | -1 -> T.make_arith T.Minus (mult_const tc c 0) tc
  | i when i > 0 -> T.make_arith T.Plus (mult_const tc c (i - 1)) tc
  | i when i < 0 -> T.make_arith T.Minus (mult_const tc c (i + 1)) tc
  | _ -> assert false

let make_arith_cs =
  MConst.fold 
    (fun c i acc ->
      let tc = make_const c in
      let tci = mult_const tc c i in
       T.make_arith T.Plus acc tci)

let make_cs cs =
  let c, i = MConst.choose cs in
  let t_c = make_const c in
  let r = MConst.remove c cs in
  if MConst.is_empty r then mult_const t_c c i
  else make_arith_cs r (mult_const t_c c i)
  
	 
let simplify_smt_atom t1 op t2 =
  let rec make_term tt = 
    match tt with 
      | Elem (e, _) ->  T.make_app e []
      | Const cs -> make_cs cs 
      | Access (a, li)  ->
	T.make_app a (List.map (fun i -> T.make_app i []) li)
      | Arith (x, cs) -> 
	let tx = make_term x in
	make_arith_cs cs tx
      | UnOp (o,t1) -> Format.eprintf "ici@."; assert false
      | BinOp (t1, op, t2) -> Format.eprintf "ici@."; assert false
	
      | Record lbs ->
	let record = Smt.Type.record_ty_by_field (fst (List.hd lbs)) in
	let ls = List.map (fun (f,t) -> make_term t) lbs in

	T.make_record record ls
      
      | RecordWith (t, htl)  ->  assert false
	
      | RecordField (record, field) ->
	let t_record = make_term record in
	let _, re = Smt.Type.record_ty_by_field field  in
	let ty_field= Hstring.list_assoc field re in
	T.make_field field t_record ty_field 
  in
  let nt1 = make_term t1 in
  let nt2 = make_term t2 in
  let rt1,_ = Combine.CX.make nt1 in
  let rt2,_ = Combine.CX.make nt2 in 
  try
    let r = Combine.CX.solve rt1 rt2 in
    if r = [] then
      if op = Eq then Some Atom.True
      else Some Atom.False
    else None
  with Exception.Unsolvable ->
    if op = Eq then Some Atom.False
    else Some Atom.True
    
