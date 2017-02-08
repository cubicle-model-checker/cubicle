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
  open Cubtypes
  open Parsing
  open Ptree
  open Util
  open Regexp.RTrans
  
  let _ = Smt.set_cc false; Smt.set_arith false; Smt.set_sum false


  (* Helper functions for location info *)

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)

  let vars_to_hsset vl = Hstring.HSet.singleton (Hstring.make "#1")

  type t = 
    | Assign of Hstring.t * pglob_update
    | Nondet of Hstring.t
    | Upd of pupdate

  module S = Set.Make(Hstring)

  module Constructors = struct
    let s = ref (S.add (Hstring.make "True") 
		   (S.singleton (Hstring.make "False")))
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

  let sort s = 
    if Constructors.mem s then Constr 
    else if Globals.mem s then Glob
    else
      begin
        assert (not (Arrays.mem s));
        Var
      end

  let hproc = Hstring.make "proc"
  let hreal = Hstring.make "real"
  let hint = Hstring.make "int"

  let set_from_list = List.fold_left (fun sa a -> SAtom.add a sa) SAtom.empty 

  let fresh_var = 
    let cpt = ref 0 in
    fun () -> incr cpt; Hstring.make ("_j"^(string_of_int !cpt))

  type tt = TT_Trans | TT_Meta | TT_Univ

%}

%token VAR ARRAY CONST TYPE INIT INVARIANT CASE
%token METATRANSITION UNIVTRANSITION HIDETRANSITION TRANSITION
%token FORALL EXISTS FORALL_OTHER EXISTS_OTHER
%token SIZEPROC TREGEXP
%token REQUIRE UNSAFE PREDICATE
%token OR AND COMMA PV DOT QMARK IMP EQUIV
%token <string> CONSTPROC
%token <string> LIDENT
%token <string> MIDENT
%token LEFTPAR RIGHTPAR COLON EQ NEQ LT LE GT GE
%token LEFTSQ RIGHTSQ LEFTBR RIGHTBR BAR 
%token <Num.num> REAL
%token <Num.num> INT
%token PLUS MINUS TIMES
%token IF THEN ELSE NOT
%token TRUE FALSE
%token UNDERSCORE AFFECT HASH
%token EOF

%nonassoc prec_forall prec_exists
%right IMP EQUIV  
%right OR
%right AND
%nonassoc prec_ite
/* %left prec_relation EQ NEQ LT LE GT GE */
/* %left PLUS MINUS */
%nonassoc NOT

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
  let pconsts, pglobals, parrays = sd in
  psystem_of_decls ~pglobals ~pconsts ~parrays ~ptype_defs dl
   |> encode_psystem 
}

decl_list :
   | d=decl+ { d }
; 

decl :
  | i=init { PInit i }
  | i=invariant { PInv i }
  | u=unsafe { PUnsafe u }
  | t=transition_decl { t }
  | ht=hide_transition { PHideTrans ht }
  | function_decl { PFun }
  | dr=decl_regexp { PRegExp dr }

symbold_decls :
  | { [], [], [] }
  | cd=const_decl sd=symbold_decls
      { let consts, vars, arrays = sd in (cd::consts), vars, arrays }
  | vd=var_decl sd=symbold_decls
      { let consts, vars, arrays = sd in consts, (vd::vars), arrays }
  | ad=array_decl sd=symbold_decls
      { let consts, vars, arrays = sd in consts, vars, (ad::arrays) }
;

elementary_regexp:
  | LEFTPAR re=regexp RIGHTPAR 
      { re }
  | tn=transition_name LEFTPAR li=lidents RIGHTPAR
      { PChar (tn, li) }

basic_regexp :
  | er=elementary_regexp
      { er }
  | er=elementary_regexp TIMES
      { PStar er }
  | er=elementary_regexp PLUS
      { PPlus er }
  | er=elementary_regexp QMARK
      { POption er }
;

union :
  | br1=basic_regexp BAR br2=basic_regexp
      { [br1; br2] }
  | br=basic_regexp BAR brl=union
      { br :: brl }
;

simple_regexp :
  | u=union
      { PUnion u }
  | br=basic_regexp
      { br }
;

concatenation :
  | s1=simple_regexp s2=simple_regexp
      { [s1; s2] }
  | s=simple_regexp c=concatenation
      { s :: c }
;

regexp :
  | c=concatenation 
      { PConcat c }
  | s=simple_regexp
      { s }
;

decl_regexp :
  | TREGEXP COLON r=regexp PV
      { r } 
;

function_decl :
  | PREDICATE lident LEFTPAR lident_comma_list RIGHTPAR LEFTBR expr RIGHTBR {
    add_fun_def $2 $4 $7
  }
;

var_decl:
  | VAR mident COLON lident { 
    if Hstring.equal $4 hint || Hstring.equal $4 hreal then Smt.set_arith true;
    Globals.add $2; 
    loc (), $2, $4 }
;

const_decl:
  | CONST mident COLON lident { 
    if Hstring.equal $4 hint || Hstring.equal $4 hreal then Smt.set_arith true;
    Consts.add $2;
    loc (), $2, $4 }
;

array_decl:
  | ARRAY mident LEFTSQ lident_list_plus RIGHTSQ COLON lident { 
        if not (List.for_all (fun p -> Hstring.equal p hproc) $4) then
          raise Parsing.Parse_error;
        if Hstring.equal $7 hint || Hstring.equal $7 hreal then Smt.set_arith true;
	Arrays.add $2;
	loc (), $2, ($4, $7)}
;

type_defs:
  | { [] }
  | type_def_plus { $1 }
;

type_def_plus:
  | type_def { [$1] }
  | type_def type_def_plus { $1::$2 }
;

size_proc:
  | { () }
  | SIZEPROC INT { Options.size_proc := Num.int_of_num $2 }
;
      
type_def:
  | TYPE lident { (loc (), ($2, [])) }
  | TYPE lident EQ constructors 
      { Smt.set_sum true; List.iter Constructors.add $4; (loc (), ($2, $4)) }
  | TYPE lident EQ BAR constructors 
      { Smt.set_sum true; List.iter Constructors.add $5; (loc (), ($2, $5)) }
;

constructors:
  | mident { [$1] }
  | mident BAR constructors { $1::$3 }
;

init:
  | INIT LEFTBR expr RIGHTBR { loc (), [], $3 } 
  | INIT LEFTPAR lidents RIGHTPAR LEFTBR expr RIGHTBR { loc (), $3, $6 }
;

invariant:
  | INVARIANT LEFTBR expr RIGHTBR { loc (), [], $3 }
  | INVARIANT LEFTPAR lidents RIGHTPAR LEFTBR expr RIGHTBR { loc (), $3, $6 }
;

unsafe:
  | UNSAFE LEFTBR expr RIGHTBR { loc (), [], $3 }
  | UNSAFE LEFTPAR lidents RIGHTPAR LEFTBR expr RIGHTBR { loc (), $3, $6 }
;

transition_name:
  | lident {$1}
  | mident {$1}
;

transition_type:
  | TRANSITION
      { TT_Trans }
  | METATRANSITION
      { TT_Meta }
  | UNIVTRANSITION
      { TT_Univ }
;

transition_decl:
  | tt=transition_type ptr_name=transition_name LEFTPAR ptr_args=lidents RIGHTPAR 
     ptr_reqs=require
     LEFTBR anu=assigns_nondets_updates RIGHTBR
      { let ptr_assigns, ptr_nondets, ptr_upds = anu in
	let trans =
          { ptr_name;
            ptr_args; 
	    ptr_reqs;
	    ptr_assigns; 
	    ptr_nondets; 
	    ptr_upds;
            ptr_loc = loc ();
          } in
        match tt with
          | TT_Trans -> PTrans trans
          | TT_Meta -> PMetaTrans trans
          | TT_Univ -> PUnivTrans trans
      }
;

hide_transition:
  | HIDETRANSITION COLON tl=transition_name* PV { tl }
;

assigns_nondets_updates:
  | { [], [], [] }
  | anu=assign_nondet_update 
      {  
	match anu with
	  | Assign (x, y) -> [x, y], [], []
	  | Nondet x -> [], [x], []
	  | Upd x -> [], [], [x]
      }
  | anu=assign_nondet_update PV anul=assigns_nondets_updates 
      { 
	let assigns, nondets, upds = anul in
	match anu with
	  | Assign (x, y) -> (x, y) :: assigns, nondets, upds
	  | Nondet x -> assigns, x :: nondets, upds
	  | Upd x -> assigns, nondets, x :: upds
      }
;

assign_nondet_update:
  | assignment { $1 }
  | nondet { $1 }
  | update { $1 }
;

assignment:
  | id=mident AFFECT t=term { Assign (id, PUTerm t) }
  | id=mident AFFECT CASE s=switchs { Assign (id, PUCase s) }
;

nondet:
  | id=mident AFFECT DOT { Nondet id }
  | id=mident AFFECT QMARK { Nondet id }
;

require:
  | { PAtom (AAtom (Atom.True)) }
  | REQUIRE LEFTBR e=expr RIGHTBR { e }
;

update:
  | id=mident LEFTSQ pnl=proc_name_list_plus RIGHTSQ AFFECT CASE sw=switchs
      { List.iter (fun p ->
          if (Hstring.view p).[0] = '#' then
            raise Parsing.Parse_error;
        ) pnl;
        Upd { pup_loc = loc (); pup_arr = id; pup_arg = pnl; pup_swts = sw} }
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
  | BAR sw=switch { [sw] }
  | BAR sw=switch swl=switchs { sw::swl }
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
  | pn=proc_name { Elem (pn, Var) }
;

top_id_term:
  | vt=var_term { match vt with
      | Elem (v, Var) -> TVar v
      | _ -> TTerm vt }
;


array_term:
  | id=mident LEFTSQ pnl=proc_name_list_plus RIGHTSQ {
    Access (id, pnl)
  }
;

var_or_array_term:
  | vt=var_term { vt }
  | at=array_term { at }
;

arith_term:
  | vat=var_or_array_term PLUS cn=constnum 
      { Arith(vat, MConst.add cn 1 MConst.empty) }
  | vat=var_or_array_term MINUS cn=constnum 
      { Arith(vat, MConst.add cn (-1) MConst.empty) }
  | vat=var_or_array_term PLUS id=mident 
      { Arith(vat, MConst.add (ConstName id) 1 MConst.empty) }
  | vat=var_or_array_term PLUS i=INT TIMES id=mident
      { Arith(vat, MConst.add (ConstName id) (Num.int_of_num i) MConst.empty) }
  | vat=var_or_array_term PLUS id=mident TIMES i=INT
      { Arith(vat, MConst.add (ConstName id) (Num.int_of_num i) MConst.empty) }
  | vat=var_or_array_term MINUS id=mident 
      { Arith(vat, MConst.add (ConstName id) (-1) MConst.empty) }
  | vat=var_or_array_term MINUS i=INT TIMES id=mident 
      { Arith(vat, MConst.add (ConstName id) (- (Num.int_of_num i)) MConst.empty) }
  | vat=var_or_array_term MINUS id=mident TIMES i=INT 
      { Arith(vat, MConst.add (ConstName id) (- (Num.int_of_num i)) MConst.empty) }
  | i=INT TIMES id=mident 
      { Const(MConst.add (ConstName id) (Num.int_of_num i) MConst.empty) }
  | MINUS i=INT TIMES id=mident 
      { Const(MConst.add (ConstName id) (- (Num.int_of_num i)) MConst.empty) }
  | cn=constnum { Const (MConst.add cn 1 MConst.empty) }
;

term:
  | id=top_id_term { id } 
  | at=array_term { TTerm at }
  | at=arith_term { Smt.set_arith true; TTerm at }
;

lident:
  | id=LIDENT { Hstring.make id }
;

const_proc:
  | cp=CONSTPROC { Hstring.make cp }
;

proc_name:
  | id=lident { id }
  | cp=const_proc { cp }
;

proc_name_list_plus:
  | pnl=separated_nonempty_list(COMMA, proc_name) { pnl }
;

mident:
  | id=MIDENT { Hstring.make id }
;

lidents:
  | idl=list(lident) { idl }
;

lident_list_plus:
  | idl=separated_nonempty_list(COMMA, lident) { idl }
;

lident_comma_list:
  | idl=separated_list(COMMA, lident) { idl }
;

lidents_plus_distinct:
  | idl=separated_nonempty_list(NEQ, lident) { idl }
;


%inline binop:
  | EQ { EQ }
  | NEQ { NEQ }
  | LT { Smt.set_arith true; LT }
  | LE { Smt.set_arith true; LE }
  | GT { Smt.set_arith true; GT }
  | GE { Smt.set_arith true; GE }

;

literal:
  | TRUE { AAtom Atom.True }
  | FALSE { AAtom Atom.False }
  /* | lident { AVar $1 } RR conflict with proc_name */
    | t1=term op=binop t2=term {
      let t1, op, t2 = match op with
        | EQ -> t1, Eq, t2
        | NEQ -> t1, Neq, t2
        | LT -> t1, Lt, t2
        | LE -> t1, Le, t2
        | GT -> t2, Lt, t1
        | GE -> t2, Le, t1
        | _ -> assert false
      in ABinop (t1, op, t2)
    }
;

expr:
  | se=simple_expr
      { se }
  | NOT e=expr
      { PNot e }
  | e1=expr AND e2=expr
      { PAnd [e1; e2] }
  | e1=expr OR e2=expr
      { POr [e1; e2] }
  | e1=expr IMP e2=expr
      { PImp (e1, e2) }
  | e1=expr EQUIV e2=expr
      { PEquiv (e1, e2) }
  | IF cond=expr THEN et=expr ELSE ee=expr %prec prec_ite
      { PIte (cond, et, ee) }
  | FORALL idl=lidents_plus_distinct DOT e=expr %prec prec_forall
      { PForall (idl, e) }
  | EXISTS idl=lidents_plus_distinct DOT e=expr %prec prec_exists
      { PExists (idl, e) }
  | FORALL_OTHER id=lident DOT e=expr %prec prec_forall
      { PForall_other ([id], e) }
  | EXISTS_OTHER id=lident DOT e=expr %prec prec_exists
      { PExists_other ([id], e) }
  | HASH LEFTBR id=lident DOT e=expr RIGHTBR op=binop rc=right_side_count
      { let op = match op with
        | EQ -> Eq
        | NEQ -> Neq
        | LT -> Lt
        | LE -> Le
        | _ -> assert false
        in
        PCount ([id], e, op, rc) }
;

right_side_count:
  | i=INT
      {MConst.add (ConstInt i) 1 MConst.empty}
  | i=INT TIMES id=mident 
      { MConst.add (ConstName id) (Num.int_of_num i) MConst.empty }
;
      
simple_expr:
  | l=literal { PAtom l }
  | LEFTPAR e=expr RIGHTPAR { e }
  | id=lident LEFTPAR etl=expr_or_term_comma_list RIGHTPAR { app_fun id etl }
;



expr_or_term_comma_list:
  | { [] }
  | t=term  { [PT t] }
  | e=expr  { [PF e] }
  | t=term COMMA etl=expr_or_term_comma_list { PT t :: etl }
  | e=expr COMMA etl=expr_or_term_comma_list { PF e :: etl }
;
