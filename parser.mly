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
%token SIZEPROC
%token REQUIRE UNSAFE PREDICATE
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
%token WITH
%token EOF

%nonassoc IN       
%nonassoc prec_forall prec_exists
%right IMP EQUIV  
%right OR
%right AND
%nonassoc prec_ite
  /* %left prec_relation EQ NEQ LT LE GT GE */
%left PLUS MINUS
%left TIMES
%nonassoc NOT
  /* %left BAR */
%left DOT

%type <Ast.system> system
%start system
%%

system:
size_proc
type_defs
symbold_decls
decl_list
EOF
{ let ptype_defs = $2 in
  Smt.set_sum true;
  let b = [Hstring.make "@MTrue"; Hstring.make "@MFalse"] in
  List.iter Constructors.add b;
  let ptype_defs = Constructors ((loc (), (Hstring.make "mbool", b))) :: ptype_defs in
  let pconsts, pglobals, parrays = $3 in
  psystem_of_decls ~pglobals ~pconsts ~parrays ~ptype_defs $4
   |> encode_psystem 
}
;

decl_list :
  | decl { [$1] }
  | decl decl_list { $1 :: $2 }
;

decl :
  | init { PInit $1 }
  | invariant { PInv $1 }
  | unsafe { PUnsafe $1 }
  | transition { PTrans $1 }
  | function_decl { PFun  }

symbold_decls :
  | { [], [], [] }
  | const_decl symbold_decls
      { let consts, vars, arrays = $2 in ($1::consts), vars, arrays }
  | var_decl symbold_decls
      { let consts, vars, arrays = $2 in consts, ($1::vars), arrays }
  | array_decl symbold_decls
      { let consts, vars, arrays = $2 in consts, vars, ($1::arrays) }
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

record_field:
  | lident COLON lident {
    if Hstring.equal $3 hint || Hstring.equal $3 hreal then Smt.set_arith true;
    ($1, $3) }
;

record_fields:
  | record_field { [$1] }
  | record_field PV { [$1] }
  | record_field PV record_fields { $1::$3 }
;
      
type_def:
  | TYPE lident { Constructors ((loc (), ($2, []))) }
  | TYPE lident EQ constructors 
      { Smt.set_sum true; List.iter Constructors.add $4; Constructors ((loc (), ($2, $4))) }
  | TYPE lident EQ BAR constructors 
      { Smt.set_sum true; List.iter Constructors.add $5; Constructors ((loc (), ($2, $5))) }
  | TYPE lident EQ LEFTBR record_fields RIGHTBR { Records (loc (), ($2, $5)) }
  
						       
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

transition:
  | TRANSITION transition_name LEFTPAR lidents RIGHTPAR 
      require
      LEFTBR let_assigns_nondets_updates RIGHTBR
      { let lets, (assigns, nondets, upds) = $8 in
	{   ptr_lets = lets;
	    ptr_name = $2;
            ptr_args = $4; 
	    ptr_reqs = $6;
	    ptr_assigns = assigns; 
	    ptr_nondets = nondets; 
	    ptr_upds = upds;
            ptr_loc = loc ();
          }
      }
;

let_assigns_nondets_updates:
  | assigns_nondets_updates { [], $1 }
  | LET lident EQ term IN let_assigns_nondets_updates {
	  let lets, l = $6 in
	  ($2, TTerm $4) :: lets, l}
;
  
assigns_nondets_updates:
  |  { [], [], [] }
  | assign_nondet_update 
      {  
	match $1 with
	  | Assign (x, y) -> [x, y,loc()], [], []
	  | Nondet x -> [], [x], []
	  | Upd x -> [], [], [x]
      }
  | assign_nondet_update PV assigns_nondets_updates 
      { 
	let assigns, nondets, upds = $3 in
	match $1 with
	  | Assign (x, y) -> (x, y, loc()) :: assigns, nondets, upds
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
  | mident AFFECT term { Assign ($1, PUTerm (TTerm $3)) }
  | mident AFFECT CASE switchs { Assign ($1, PUCase $4) }
;

nondet:
  | mident AFFECT DOT { Nondet $1 }
  | mident AFFECT QMARK { Nondet $1 }
;

require:
  | { PAtom (AAtom (Atom.True)),loc() }
  | REQUIRE LEFTBR expr RIGHTBR { $3,loc() }
;

update:
  | mident LEFTSQ proc_name_list_plus RIGHTSQ AFFECT CASE switchs
      { List.iter (fun p ->
          if (Hstring.view p).[0] = '#' then
            raise Parsing.Parse_error;
        ) $3;
        Upd { pup_loc = loc (); pup_arr = $1; pup_arg = $3; pup_swts = $7} }
  | mident LEFTSQ proc_name_list_plus RIGHTSQ AFFECT term
      { let cube, rjs =
          List.fold_left (fun (cube, rjs) i ->
            let j = fresh_var () in
            let c = PAtom (AEq (TVar j, TVar i)) in
            c :: cube, j :: rjs) ([], []) $3 in
        let a = PAnd cube in
        let js = List.rev rjs in
	let sw = [(a, TTerm $6); (PAtom (AAtom Atom.True), TTerm (Access($1, js)))] in
	Upd { pup_loc = loc (); pup_arr = $1; pup_arg = js; pup_swts = sw}  }

;

field:
  | lident EQ term { ($1, $3)}
;
field_list:
  | field { [$1] }
  | field PV { [$1] }
  | field PV field_list { $1::$3 }
;

switchs:
  | BAR UNDERSCORE COLON term { [(PAtom (AAtom (Atom.True)), TTerm $4)] }
  | BAR switch { [$2] }
  | BAR switch switchs { $2::$3 }
;

switch:
  | expr COLON term { $1, TTerm $3 }
;

  

term:
  | REAL { Const (MConst.add (ConstReal $1) 1 MConst.empty) }
  | INT { Const (MConst.add (ConstInt $1) 1 MConst.empty) }
  | proc_name { Elem ($1, Var) }
  | mident {
	let t = if Consts.mem $1 then Const (MConst.add (ConstName $1) 1 MConst.empty)
		else Elem ($1, sort $1) in  t
      }
  | mident LEFTSQ proc_name_list_plus RIGHTSQ { Access ($1, $3) }

  /*
  | MINUS term { UnOp(UMinus, $2) }
  | term PLUS term { BinOp($1, Addition, $3) }
  | term MINUS term { BinOp($1, Subtraction, $3) }
  | term TIMES term {  BinOp($1, Multiplication, $3) }
 */


  | term PLUS INT { Arith($1, MConst.add (ConstInt $3) 1 MConst.empty) }
  | term PLUS mident { Arith($1, MConst.add (ConstName $3) 1 MConst.empty) }
  | term MINUS INT { Arith($1, MConst.add (ConstInt $3) (-1) MConst.empty) }
  | term MINUS mident { Arith($1, MConst.add (ConstName $3) (-1) MConst.empty) }
   
      
  | LEFTPAR term RIGHTPAR { $2 }
  | LEFTBR term WITH field_list RIGHTBR { RecordWith($2, $4) }
  | term DOT lident { RecordField($1, $3) }
  | LEFTBR field_list RIGHTBR { Record($2) }

;

lident:
  | LIDENT { Hstring.make $1 }
;

const_proc:
  | CONSTPROC { Hstring.make $1 }
;

proc_name:
  | lident { $1 }
  | const_proc { $1 }
;

proc_name_list_plus:
  | proc_name { [$1] }
  | proc_name COMMA proc_name_list_plus { $1::$3 }
;

mident:
  | MIDENT { Hstring.make $1 }
;

lidents_plus:
  | lident { [$1] }
  | lident lidents_plus { $1::$2 }
;

lidents:
  | { [] }
  | lidents_plus { $1 }
;

lident_list_plus:
  | lident { [$1] }
  | lident COMMA lident_list_plus { $1::$3 }
;


lident_comma_list:
  | { [] }
  | lident_list_plus { $1 }
;

lidents_plus_distinct:
  | lident { [$1] }
  | lident NEQ lidents_plus_distinct { $1 :: $3 }
;


/*
operator:
  | EQ { Eq }
  | NEQ { Neq }
  | LT { Smt.set_arith true; Lt }
  | LE { Smt.set_arith true; Le }
;
*/

literal:
  | TRUE { AAtom Atom.True }
  | FALSE { AAtom Atom.False }
  /* | lident { AVar $1 } RR conflict with proc_name */
  | term EQ term { AEq (TTerm $1, TTerm $3) }
  | term NEQ term { ANeq (TTerm $1, TTerm $3) }
  | term LT term { Smt.set_arith true; ALt (TTerm $1, TTerm $3) }
  | term LE term { Smt.set_arith true; ALe (TTerm $1, TTerm $3) }
  | term GT term { Smt.set_arith true; ALt (TTerm $3, TTerm $1) }
  | term GE term { Smt.set_arith true; ALe (TTerm $3, TTerm $1) }
;

expr:
  | simple_expr { $1 }
  | NOT expr { PNot $2 }
  | expr AND expr { PAnd [$1; $3] }
  | expr OR expr  { POr [$1; $3] }
  | expr IMP expr { PImp ($1, $3) }
  | expr EQUIV expr { PEquiv ($1, $3) }
  | IF expr THEN expr ELSE expr %prec prec_ite { PIte ($2, $4, $6) }
  | FORALL lidents_plus_distinct DOT expr %prec prec_forall { PForall ($2, $4) }
  | EXISTS lidents_plus_distinct DOT expr %prec prec_exists { PExists ($2, $4) }
  | FORALL_OTHER lident DOT expr %prec prec_forall { PForall_other ([$2], $4) }
  | EXISTS_OTHER lident DOT expr %prec prec_exists { PExists_other ([$2], $4) }
;

simple_expr:
  | literal { PAtom $1 }
  | LEFTPAR expr RIGHTPAR { $2 }
  | lident LEFTPAR expr_or_term_comma_list RIGHTPAR { app_fun $1 $3 }
;


expr_or_term_comma_list:
  | { [] }
  | term  { [PT (TTerm $1)] }
  | expr  { [PF $1] }
  | term COMMA expr_or_term_comma_list { PT (TTerm $1) :: $3 }
  | expr COMMA expr_or_term_comma_list { PF $1 :: $3 }
;



