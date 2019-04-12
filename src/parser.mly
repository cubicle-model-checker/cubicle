/**************************************************************************/
/*                                                                        */
/*                              Cubicle                                   */
/*                                                                        */
/*                       Copyright (C) 2011-2014                          */
/*                                                                        */
/*                  Sylvain Conchon and Alain Mebsout                     */
/*                       Universite Paris-Sud 11                          */
/*                                                                        */
/*                                                                        */
/*  This file is distributed under the terms of the Apache Software       */
/*  License version 2.0                                                   */
/*                                                                        */
/**************************************************************************/

%{

  open Ast
  open Types
  open Parsing
  open Ptree

  let _ = Smt.set_cc false; Smt.set_arith false; Smt.set_sum false


  (* Helper functions for location info *)

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)

  type pop = PEq | PNeq | PLe | PLt | PGe | PGt

  let pop_to_op t1 t2 = function
    | PEq -> t1, t2, Eq
    | PNeq -> t1, t2, Neq
    | PLe -> t1, t2, Le
    | PLt -> t1, t2, Lt
    | PGe -> t2, t1, Le
    | PGt -> t2, t1, Lt


  type t =
    | Assign of Hstring.t * pglob_update
    | Nondet of Hstring.t
    | Upd of pupdate

  module S = Set.Make(Hstring)

  module Constructors = struct
    let s = ref (S.add (Hstring.make "@MTrue")
		   (S.singleton (Hstring.make "@MFalse")))
    let add x = s := S.add x !s
    let mem x = S.mem x !s
  end

  module Globals = struct
    let s = ref S.empty
    let add x = s := S.add x !s
    let mem x = S.mem x !s
  end

  module Arrays = struct
    let s = ref S.empty
    let add x = s := S.add x !s
    let mem x = S.mem x !s
  end

  module Consts = struct
    let s = ref S.empty
    let add x = s := S.add x !s
    let mem x = S.mem x !s
  end

  let coef = function Plus -> 1 | Minus -> -1

  let sort s =
    if Constructors.mem s then Constr
    else if Globals.mem s then Glob
    else
      begin
        (* assert (not (Arrays.mem s)); *)
        Var
      end

  let hproc = Hstring.make "proc"
  let hreal = Hstring.make "real"
  let hint = Hstring.make "int"

  let set_from_list = List.fold_left (fun sa a -> SAtom.add a sa) SAtom.empty

  let fresh_var =
    let cpt = ref 0 in
    fun () -> incr cpt; Hstring.make ("_j"^(string_of_int !cpt))

%}

%token VAR ARRAY CONST TYPE INIT TRANSITION INVARIANT CASE
%token FORALL EXISTS FORALL_OTHER EXISTS_OTHER
%token SIZEPROC WHY3
%token REQUIRE UNIVUNSAFE UNSAFE PREDICATE
%token OR AND COMMA PV DOT QMARK IMP EQUIV
%token <string> CONSTPROC
%token <string> LIDENT
%token <string> MIDENT
%token LEFTPAR RIGHTPAR COLON EQ NEQ LT LE GT GE
%token LEFTSQ RIGHTSQ LEFTBR RIGHTBR BAR
%token IN
%token LET
%token <Num.num> REAL
%token <Num.num> INT
%token PLUS MINUS TIMES
%token IF THEN ELSE NOT
%token TRUE FALSE
%token UNDERSCORE AFFECT
%token EOF

(* %nonassoc IN *)
%nonassoc prec_forall prec_exists
%right IMP EQUIV
%right OR
%right AND
%nonassoc prec_ite
/* %left prec_relation EQ NEQ LT LE GT GE */
/* %left PLUS MINUS */
%nonassoc NOT
/* %left BAR */

%type <Ast.system> system
%start system
%%

system:
size_proc
td=type_defs
sd=symbold_decls
dl=decl_list
EOF
{ let ptype_defs = td in
  Smt.set_sum true;
  let b = [Hstring.make "@MTrue"; Hstring.make "@MFalse"] in
  List.iter Constructors.add b;
  let ptype_defs = (loc (), (Hstring.make "mbool", b)) :: ptype_defs in
  let pconsts, pglobals, parrays = sd in
  psystem_of_decls ~pglobals ~pconsts ~parrays ~ptype_defs dl
   |> encode_psystem
}
;

decl_list :
  | dl=list(decl) { dl }
;

decl :
  | i=init { PInit i }
  | i=invariant { PInv i }
  | u=unsafe { PUnsafe u }
  | uu=univ_unsafe { PUnivUnsafe uu }
  | t=transition { PTrans t }
  | function_decl { PFun }
  | w=why3_invariant { PWhyInv w }
;

why3_invariant :
  | WHY3 LEFTBR e=expr RIGHTBR { loc (), [], e }
  | WHY3 LEFTPAR li=lidents RIGHTPAR LEFTBR e=expr RIGHTBR { loc (), li, e }
;

symbold_decls :
  | { [], [], [] }
  | cd=const_decl sd=symbold_decls
      { let consts, vars, arrays = sd in (cd::consts), vars, arrays }
  | vd=var_decl sd=symbold_decls
      { let consts, vars, arrays = sd in consts, (vd::vars), arrays }
  | ad=array_decl sd=symbold_decls
      { let consts, vars, arrays = sd in consts, vars, (ad::arrays) }
;

function_decl :
  | PREDICATE lid=lident LEFTPAR lidl=lident_comma_list RIGHTPAR LEFTBR e=expr RIGHTBR {
    add_fun_def lid lidl e
  }
;

var_decl:
  | VAR mid=mident COLON lid=lident {
    if Hstring.equal lid hint || Hstring.equal lid hreal then Smt.set_arith true;
    Globals.add mid;
    loc (), mid, lid }
;

const_decl:
  | CONST mid=mident COLON lid=lident {
    if Hstring.equal lid hint || Hstring.equal lid hreal then Smt.set_arith true;
    Consts.add mid;
    loc (), mid, lid }
;

array_decl:
  | ARRAY mid=mident LEFTSQ lidl=lident_comma_list_plus RIGHTSQ COLON lid=lident {
        if not (List.for_all (fun p -> Hstring.equal p hproc) lidl) then
          raise Parsing.Parse_error;
        if Hstring.equal lid hint || Hstring.equal lid hreal then Smt.set_arith true;
	Arrays.add mid;
	loc (), mid, (lidl, lid)}
;

type_defs:
  | l=type_def* { l }
;

size_proc:
  | { () }
  | SIZEPROC INT { Options.size_proc := Num.int_of_num $2 }
;

type_def:
  | TYPE li=lident { (loc (), (li, [])) }
  | TYPE li=lident EQ cs=constructors
      { Smt.set_sum true; List.iter Constructors.add cs; (loc (), (li, cs)) }
  | TYPE li=lident EQ BAR cs=constructors
      { Smt.set_sum true; List.iter Constructors.add cs; (loc (), (li, cs)) }
;

constructors:
  | l=separated_nonempty_list(BAR, mident) { l }
;

init:
  | INIT LEFTBR e=expr RIGHTBR { loc (), [], e }
  | INIT LEFTPAR ls=lidents RIGHTPAR LEFTBR e=expr RIGHTBR { loc (), ls, e }
;

invariant:
  | INVARIANT LEFTBR e=expr RIGHTBR { loc (), [], e }
  | INVARIANT LEFTPAR li=lidents RIGHTPAR LEFTBR e=expr RIGHTBR { loc (), li, e }
  (* | INVARIANT LEFTBR e=card_expr RIGHTBR { loc (), [], e } *)
;

(* card_expr: *)
(*   | literal EQ term { AEq ($1, $3) } *)
(*   | literal NEQ term { ANeq ($1, $3) } *)
(*   | literal LT term { Smt.set_arith true; ALt ($1, $3) } *)
(*   | literal LE term { Smt.set_arith true; ALe ($1, $3) } *)
(*   | literal GT term { Smt.set_arith true; ALt ($3, $1) } *)
(*   | literal GE term { Smt.set_arith true; ALe ($3, $1) } *)

(* ; *)
unsafe:
  | UNSAFE LEFTBR e=expr RIGHTBR { loc (), [], e }
  | UNSAFE LEFTPAR li=lidents RIGHTPAR LEFTBR e=expr RIGHTBR { loc (), li, e }
;

univ_unsafe:
  | UNIVUNSAFE LEFTPAR i=lident RIGHTPAR LEFTBR e=expr RIGHTBR { loc (), [], i, e }
  | UNIVUNSAFE LEFTPAR li=lidents COMMA i=lident RIGHTPAR LEFTBR e=expr RIGHTBR { loc (), li, i, e }
;

transition_name:
  | li=lident { li }
  | mi=mident { mi }

transition:
  | TRANSITION ptr_name=transition_name LEFTPAR ptr_args=lidents RIGHTPAR
     ptr_reqs=require
     LEFTBR upd=let_assigns_nondets_updates RIGHTBR
     { let ptr_lets, (ptr_assigns, ptr_nondets, ptr_upds) = upd in
       {   ptr_lets;
	   ptr_name;
           ptr_args;
	   ptr_reqs;
	   ptr_assigns;
	   ptr_nondets;
	   ptr_upds;
           ptr_loc = loc ();
       }
     }
;

let_assigns_nondets_updates:
  | upd=assigns_nondets_updates { [], upd }
  | LET li=lident EQ t=term IN llet=let_assigns_nondets_updates {
	  let lets, l = llet in
	  (li, t) :: lets, l}
;

assigns_nondets_updates:
  |  { [], [], [] }
  | a=assign_nondet_update
      {
	match a with
	  | Assign (x, y) -> [x, y], [], []
	  | Nondet x -> [], [x], []
	  | Upd x -> [], [], [x]
      }
  | a=assign_nondet_update PV al=assigns_nondets_updates
      {
	let assigns, nondets, upds = al in
	match a with
	  | Assign (x, y) -> (x, y) :: assigns, nondets, upds
	  | Nondet x -> assigns, x :: nondets, upds
	  | Upd x -> assigns, nondets, x :: upds
      }
;

assign_nondet_update:
  | a=assignment { a }
  | n=nondet { n }
  | u=update { u }
;

assignment:
  | mi=mident AFFECT t=term { Assign (mi, PUTerm t) }
  | mi=mident AFFECT CASE s=switchs { Assign (mi, PUCase s) }
;

nondet:
  | mi=mident AFFECT nondet_end { Nondet mi }
;

%inline nondet_end:
  | DOT      { }
  | QMARK    { }
;

require:
  | { PAtom (AAtom (Atom.True)) }
  | REQUIRE LEFTBR e=expr RIGHTBR { e }
;

update:
  | pup_arr=mident LEFTSQ pnl=proc_name_list_plus RIGHTSQ AFFECT CASE pup_swts=switchs
      { List.iter (fun p ->
          if (Hstring.view p).[0] = '#' then
            raise Parsing.Parse_error;
        ) pnl;
        Upd { pup_loc = loc (); pup_arr; pup_arg = pnl; pup_swts} }
  | id=mident LEFTSQ pnl=proc_name_list_plus RIGHTSQ AFFECT t=term
      { let cube, rjs =
          List.fold_left (fun (cube, rjs) i ->
            let j = fresh_var () in
            let c = PAtom (ABinop (TVar j, Eq, TVar i)) in
            c :: cube, j :: rjs) ([], []) pnl in
        let a = PAnd cube in
        let js = List.rev rjs in
	let sw = [(a, t); (PAtom (AAtom Atom.True), TTerm (Access(id, js)))] in
	Upd { pup_loc = loc (); pup_arr = id; pup_arg = js; pup_swts = sw}  }
;

switchs:
  | BAR UNDERSCORE COLON t=term { [(PAtom (AAtom (Atom.True)), t)] }
  | BAR s=switch { [s] }
  | BAR s=switch sl=switchs { s::sl }
;

switch:
  | e=expr COLON t=term { e, t }
;


constnum:
  | r=REAL { ConstReal r }
  | i=INT { ConstInt i }
;

var_term:
  | id=mident {
      if Consts.mem id then Const (MConst.add (ConstName id) 1 MConst.empty)
      else Elem (id, sort id) }
  | id=proc_name { Elem (id, Var) }
;

top_id_term:
  | id=var_term {
    match id with
      | Elem (v, Var) -> TVar v
      | _ -> TTerm id }
;

array_term:
  | id=mident LEFTSQ pnl=proc_name_list_plus RIGHTSQ {
    Access (id, pnl)
  }
;

var_or_array_term:
  | t=var_term { t }
  | t=array_term { t }
;

%inline ar_binop:
      | PLUS { Plus }
      | MINUS { Minus }
;

arith_term:
  | t=var_or_array_term op=ar_binop c=constnum
     { Arith(t, MConst.add c (coef op) MConst.empty) }
  | t=var_or_array_term op=ar_binop id=mident
      { Arith(t, MConst.add (ConstName id) (coef op) MConst.empty) }
  | t=var_or_array_term op=ar_binop i=INT TIMES id=mident
  | t=var_or_array_term op=ar_binop id=mident TIMES i=INT
      { Arith(t, MConst.add (ConstName id) ((coef op) * Num.int_of_num i) MConst.empty) }
  | i=INT TIMES id=mident
      { Const(MConst.add (ConstName id) (Num.int_of_num i) MConst.empty) }
  | MINUS i=INT TIMES id=mident
      { Const(MConst.add (ConstName id) (- (Num.int_of_num i)) MConst.empty) }
  | c=constnum { Const (MConst.add c 1 MConst.empty) }
;

term:
  | t=top_id_term { t }
  | t=array_term { TTerm t }
  | t=arith_term { Smt.set_arith true; TTerm t }
  ;

lident:
  | id=LIDENT { Hstring.make id }
;

const_proc:
  | c=CONSTPROC { Hstring.make c }
;

proc_name:
  | id=lident { id }
  | c=const_proc { c }
;

proc_name_list_plus:
  | l=separated_nonempty_list(COMMA, proc_name) { l }
;

mident:
  | id=MIDENT { Hstring.make id }
;

lidents:
  | l=list(lident){ l }
;

lident_comma_list_plus:
  | l=separated_nonempty_list(COMMA, lident) { l }
;


lident_comma_list:
  | l=separated_list(COMMA, lident) { l }
;

lidents_plus_distinct:
  | l=separated_nonempty_list(NEQ, lident) { l }
;

%inline cmp_binop:
  | EQ { PEq }
  | NEQ { PNeq }
  | LT { Smt.set_arith true; PLt }
  | LE { Smt.set_arith true; PLe }
  | GT { Smt.set_arith true; PGt }
  | GE { Smt.set_arith true; PGe }

;


literal:
  | TRUE { AAtom Atom.True }
  | FALSE { AAtom Atom.False }
    /* | lident { AVar $1 } RR conflict with proc_name */
  | t1=term pop=cmp_binop t2=term {
      let t1, t2, op = pop_to_op t1 t2 pop in
      ABinop (t1, op, t2)
    }

  /*| term EQ term { AEq ($1, $3) }
  | term NEQ term { ANeq ($1, $3) }
  | term LT term { Smt.set_arith true; ALt ($1, $3) }
  | term LE term { Smt.set_arith true; ALe ($1, $3) }
  | term GT term { Smt.set_arith true; ALt ($3, $1) }
  | term GE term { Smt.set_arith true; ALe ($3, $1) }*/
;

expr:
  | e=simple_expr { e }
  | NOT e=expr { PNot e }
  | e1=expr AND e2=expr { PAnd [e1; e2] }
  | e1=expr OR e2=expr  { POr [e1; e2] }
  | e1=expr IMP e2=expr { PImp (e1, e2) }
  | e1=expr EQUIV e2=expr { PEquiv (e1, e2) }
  | IF cond=expr THEN et=expr ELSE ee=expr %prec prec_ite { PIte (cond, et, ee) }
  | FORALL idl=lidents_plus_distinct DOT e=expr %prec prec_forall { PForall (idl, e) }
  | EXISTS idl=lidents_plus_distinct DOT e=expr %prec prec_exists { PExists (idl, e) }
  | FORALL_OTHER id=lident DOT e=expr %prec prec_forall { PForall_other ([id], e) }
  | EXISTS_OTHER id=lident DOT e=expr %prec prec_exists { PExists_other ([id], e) }
;

simple_expr:
  | l=literal { PAtom l }
  | LEFTPAR e=expr RIGHTPAR { e }
  | id=lident LEFTPAR etl=expr_or_term_comma_list RIGHTPAR { app_fun id etl }
;

%inline expr_or_term:
  | t=term { PT t }
  | e=expr { PF e }
;

expr_or_term_comma_list:
  | l = separated_list(COMMA, expr_or_term) { l }
;
