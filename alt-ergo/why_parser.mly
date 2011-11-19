/**************************************************************************/
/*                                                                        */
/*     The Alt-ergo theorem prover                                        */
/*     Copyright (C) 2006-2010                                            */
/*                                                                        */
/*     Sylvain Conchon                                                    */
/*     Evelyne Contejean                                                  */
/*     Stephane Lescuyer                                                  */
/*     Mohamed Iguernelala                                                */
/*     Alain Mebsout                                                      */
/*                                                                        */
/*     CNRS - INRIA - Universite Paris Sud                                */
/*                                                                        */
/*   This file is distributed under the terms of the CeCILL-C licence     */
/*                                                                        */
/**************************************************************************/

/*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 */

/* from http://www.lysator.liu.se/c/ANSI-C-grammar-y.html */

%{

  open Why_ptree
  open Parsing
  open Format
  open Options

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)

  let mk_ppl loc d = { pp_loc = loc; pp_desc = d }
  let mk_pp d = mk_ppl (loc ()) d
  let mk_pp_i i d = mk_ppl (loc_i i) d
		    
  let infix_ppl loc a i b = mk_ppl loc (PPinfix (a, i, b))
  let infix_pp a i b = infix_ppl (loc ()) a i b

  let prefix_ppl loc p a = mk_ppl loc (PPprefix (p, a))
  let prefix_pp p a = prefix_ppl (loc ()) p a

  let check_binary_mode s = 
    String.iter (fun x-> if x<>'0' && x<>'1' then raise Parsing.Parse_error) s;
    s

%}

/* Tokens */ 

%token <string> IDENT
%token <string> INTEGER
%token <string> FLOAT
%token <Num.num> NUM
%token <string> STRING
%token WITH
%token AND LEFTARROW ARROW AC AT AXIOM REWRITING
%token BAR HAT
%token BOOL COLON COMMA PV DISTINCT DOT ELSE EOF EQUAL
%token EXISTS FALSE VOID FORALL FUNCTION GE GOAL GT
%token IF IN INT BITV
%token LE LET LEFTPAR LEFTSQ LEFTBR LOGIC LRARROW LT MINUS 
%token NOT NOTEQ OR PERCENT PLUS PREDICATE PROP 
%token QUOTE REAL UNIT
%token RIGHTPAR RIGHTSQ RIGHTBR
%token SLASH 
%token THEN TIMES TRUE TYPE
%token REACH

/* Precedences */

%nonassoc IN
%nonassoc prec_forall prec_exists
%right ARROW LRARROW
%right OR
%right AND 
%nonassoc prec_ite
%left prec_relation EQUAL NOTEQ LT LE GT GE
%left PLUS MINUS
%left TIMES SLASH PERCENT AT
%nonassoc HAT
%nonassoc uminus
%nonassoc NOT DOT
%right prec_named
%left LEFTSQ
%nonassoc LIDENT

/* Entry points */

%type <Why_ptree.lexpr list> trigger
%start trigger
%type <Why_ptree.lexpr> lexpr
%start lexpr
%type <Why_ptree.file> file
%start file
%%

file:
| list1_decl EOF 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-file@.";
     $1 }
| EOF 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-file@.";
     [] }
;

list1_decl:
| decl 
   { [$1] }
| decl list1_decl 
   { $1 :: $2 }
;

decl:
| TYPE type_vars ident
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     TypeDecl (loc_ij 1 2, $2, $3, Abstract) }
| TYPE type_vars ident EQUAL list1_constructors_sep_bar
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     TypeDecl (loc_i 2, $2, $3, Enum $5 ) }
| TYPE type_vars ident EQUAL record_type
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     TypeDecl (loc_i 2, $2, $3, Record $5 ) }
| LOGIC ac_modifier list1_ident_sep_comma COLON logic_type
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     Logic (loc (), $2, $3, $5) }
| FUNCTION ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR COLON 
  primitive_type EQUAL lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     Function_def (loc (), $2, $4, $7, $9) }
| PREDICATE ident EQUAL lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     Predicate_def (loc (), $2, [], $4) }
| PREDICATE ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR EQUAL lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     Predicate_def (loc (), $2, $4, $7) }
| AXIOM ident COLON lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     Axiom (loc (), $2, $4) }
| REWRITING ident COLON list1_lexpr_sep_pv
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     Rewriting(loc (), $2, $4) }
| GOAL ident COLON lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-decl@.";
     Goal (loc (), $2, $4) }
;

ac_modifier:
  /* */ { Symbols.Other }
| AC    { Symbols.Ac }

primitive_type:
| INT 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-primitive-type@.";
     PPTint }
| BOOL 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-primitive-type@.";
     PPTbool }
| REAL 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-primitive-type@.";
     PPTreal }
| UNIT 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-primitive-type@.";
     PPTunit }
| BITV LEFTSQ INTEGER RIGHTSQ
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-primitive-type@.";
     PPTbitv(int_of_string $3) }
| ident 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-primitive-type@.";
     PPTexternal ([], $1, loc ()) }
| type_var 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-primitive-type@.";
     PPTvarid ($1, loc ()) }
| primitive_type ident
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-primitive-type@.";
     PPTexternal ([$1], $2, loc_i 2) }
| LEFTPAR list1_primitive_type_sep_comma RIGHTPAR ident
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-primitive-type@.";
     PPTexternal ($2, $4, loc_i 4) }
;

logic_type:
| list0_primitive_type_sep_comma ARROW PROP
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-logic-type@.";
     PPredicate $1 }
| PROP
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-logic-type@.";
     PPredicate [] }
| list0_primitive_type_sep_comma ARROW primitive_type
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-logic-type@.";
     PFunction ($1, $3) }
| primitive_type
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-logic-type@.";
     PFunction ([], $1) }
;

list1_primitive_type_sep_comma:
| primitive_type                                      { [$1] }
| primitive_type COMMA list1_primitive_type_sep_comma { $1 :: $3 }
;

list0_primitive_type_sep_comma:
| /* epsilon */                  { [] }
| list1_primitive_type_sep_comma { $1 }
;

list0_logic_binder_sep_comma:
| /* epsilon */                { [] }
| list1_logic_binder_sep_comma { $1 }
;

list1_logic_binder_sep_comma:
| logic_binder                                    { [$1] }
| logic_binder COMMA list1_logic_binder_sep_comma { $1 :: $3 }
;

logic_binder:
| ident COLON primitive_type       
    { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-logic-binder@.";
     (loc_i 1, $1, $3) }
;

list1_constructors_sep_bar:
| ident { [$1] }
| ident BAR list1_constructors_sep_bar { $1 :: $3}
;


lexpr:

| simple_expr { $1 }

/* binary operators */

| lexpr PLUS lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 PPadd $3 }
| lexpr MINUS lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 PPsub $3 }
| lexpr TIMES lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 PPmul $3 }
| lexpr SLASH lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 PPdiv $3 }
| lexpr PERCENT lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 PPmod $3 }
| lexpr AND lexpr 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 PPand $3 }
| lexpr OR lexpr 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 PPor $3 }
| lexpr LRARROW lexpr 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 PPiff $3 }
| lexpr ARROW lexpr 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 PPimplies $3 }
| lexpr relation lexpr %prec prec_relation
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     infix_pp $1 $2 $3 }

/* unary operators */

| NOT lexpr 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     prefix_pp PPnot $2 }
| MINUS lexpr %prec uminus
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     prefix_pp PPneg $2 }

/* bit vectors */

| LEFTSQ BAR INTEGER BAR RIGHTSQ
    { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-bitv@.";
      if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
      mk_pp (PPconst (ConstBitv (check_binary_mode $3))) }
| lexpr HAT LEFTBR INTEGER COMMA INTEGER RIGHTBR
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     let i =  mk_pp (PPconst (ConstInt $4)) in
     let j =  mk_pp (PPconst (ConstInt $6)) in
     mk_pp (PPextract ($1, i, j)) }
| lexpr AT lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPconcat($1, $3)) }

/* predicate or function calls */

| DISTINCT LEFTPAR list2_lexpr_sep_comma RIGHTPAR 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPdistinct $3) }


| IF lexpr THEN lexpr ELSE lexpr %prec prec_ite
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPif ($2, $4, $6)) }

| FORALL list1_ident_sep_comma COLON primitive_type triggers 
  DOT lexpr %prec prec_forall
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPforall ($2, $4, $5, $7)) }

| EXISTS list1_ident_sep_comma COLON primitive_type DOT lexpr %prec prec_exists
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPexists ($2, $4, $6)) }

| ident_or_string COLON lexpr %prec prec_named
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPnamed ($1, $3)) }

| LET ident EQUAL lexpr IN lexpr
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPlet ($2, $4, $6)) }
;

simple_expr : 

/* constants */
| INTEGER
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPconst (ConstInt $1)) }
| NUM
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPconst (ConstReal $1)) }
| TRUE
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPconst ConstTrue) }
| FALSE
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPconst ConstFalse) }    
| VOID 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPconst ConstVoid) }    
| ident
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPvar $1) }

/* records */

| LEFTBR list1_label_expr_sep_PV RIGHTBR
   { mk_pp (PPrecord $2) }

| LEFTBR simple_expr WITH list1_label_expr_sep_PV RIGHTBR
    { mk_pp (PPwith($2, $4)) }

| simple_expr DOT ident
   { mk_pp (PPdot($1, $3)) }

/* function or predicat calls */

| ident LEFTPAR list0_lexpr_sep_comma RIGHTPAR 
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     mk_pp (PPapp ($1, $3)) }


/* arrays */

| simple_expr LEFTSQ lexpr RIGHTSQ
    { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
      mk_pp(PPget($1, $3)) }
| simple_expr LEFTSQ array_assignements RIGHTSQ
    { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
      let acc, l = match $3 with
	| [] -> assert false
	| (i, v)::l -> mk_pp (PPset($1, i, v)), l 
      in
      List.fold_left (fun acc (i,v) -> mk_pp (PPset(acc, i, v))) acc l
    }

| LEFTPAR lexpr RIGHTPAR
   { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-expr@.";
     $2 }
;

array_assignements:
| array_assignement { [$1] }
| array_assignement COMMA array_assignements { $1 :: $3 }
;

array_assignement:
|  lexpr LEFTARROW lexpr { $1, $3 }
;

triggers:
| /* epsilon */ 
    { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-triggers@.";
      [] }
| LEFTSQ list1_trigger_sep_bar RIGHTSQ 
    { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-triggers@.";
      $2 }
;

list1_trigger_sep_bar:
| trigger { [$1] }
| trigger BAR list1_trigger_sep_bar { $1 :: $3 }
;

trigger:
  list1_lexpr_sep_comma 
     { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-trigger@.";
       $1 }
;


list1_lexpr_sep_pv:
| lexpr                       { [$1] }
| lexpr PV                    { [$1] }
| lexpr PV list1_lexpr_sep_pv { $1 :: $3 }
;

list0_lexpr_sep_comma:
| /*empty */                        { [] }
| lexpr                             { [$1] }
| lexpr COMMA list1_lexpr_sep_comma { $1 :: $3 }
;

list1_lexpr_sep_comma:
| lexpr                             { [$1] }
| lexpr COMMA list1_lexpr_sep_comma { $1 :: $3 }
;

list2_lexpr_sep_comma:
| lexpr COMMA lexpr                 { [$1; $3] }
| lexpr COMMA list2_lexpr_sep_comma { $1 :: $3 }
;

relation:
| LT { PPlt }
| LE { PPle }
| GT { PPgt }
| GE { PPge }
| EQUAL { PPeq }
| NOTEQ { PPneq }
;

record_type:
| LEFTBR list1_label_sep_PV RIGHTBR
   { $2 }
;

list1_label_sep_PV:
| label_with_type                         { [$1] }
| label_with_type PV list1_label_sep_PV   { $1::$3 }
;

label_with_type:
| ident COLON primitive_type
   { $1,$3 }
;


list1_label_expr_sep_PV:
| ident EQUAL lexpr
   { [$1, $3] }
| ident EQUAL lexpr PV list1_label_expr_sep_PV
   { ($1, $3) :: $5 }
;

type_var:
| QUOTE ident 
    { if qualif = 0 then fprintf fmt "[rule] TR-Lexical-car-type@.";
      $2 }
;

type_vars:
| /* empty */
  { [] }
| type_var 
   { [$1] }
| LEFTPAR list1_type_var_sep_comma RIGHTPAR 
   { $2 }

list1_type_var_sep_comma:
| type_var                                { [$1] }
| type_var COMMA list1_type_var_sep_comma { $1 :: $3 }
;

ident:
| IDENT { $1 }
;

list1_ident_sep_comma:
| ident                             { [$1] }
| ident COMMA list1_ident_sep_comma { $1 :: $3 }
;

ident_or_string:
| IDENT  { $1 }
| STRING { $1 }
;

