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

%{
  open Smt_ast

  let loc () = symbol_start_pos (), symbol_end_pos ()

  let mk_term t = { term = t; tloc = loc () }

  let mk_form f = { formula = f; floc = loc () }

  let status = ref Unknown

%}

%token BENCHMARK
%token LOGIC
%token THEORY

/* attributes */
%token ASSUMPTION_ATRB 
%token AXIOMS_ATRB 
%token DEFINITION_ATRB 
%token EXTENSIONS_ATRB 
%token FORMULA_ATRB
%token FUNS_ATRB 
%token EXTRAFUNS_ATRB 
%token EXTRASORTS_ATRB
%token EXTRAPREDS_ATRB 
%token LANGUAGE_ATRB
%token LOGIC_ATRB
%token NOTES_ATRB
%token PREDS_ATRB
%token REWRITING_ATRB 
%token SORTS_ATRB 
%token STATUS_ATRB 
%token THEORY_ATRB 
%token <string> ATTRIBUTE

/* status */
%token SAT UNSAT UNKNOWN

/* symbols */
%token <string> NUMERAL
%token <string> RATIONAL
%token <string> ID
%token <string> ARSYMB
%token <string> USER_VALUE
%token <string> VAR
%token <string> FVAR
%token <string> STRING

/* predicates */
%token EQUALS
%token DISTINCT

/* connectives */
%token ITE
%token NOT
%token IMPLIES
%token IFTHENELSE
%token AND OR XOR
%token IFF

/* formulas */
%token TRUE FALSE
%token EXISTS FORALL
%token LET FLET

/* misc */
%token LP RP
%token EOF


%start benchmark logic theory
%type <Smt_ast.pbench> benchmark
%type <Smt_ast.plogic> logic
%type <Smt_ast.ptheory> theory

%%

theory:
| LP THEORY ID theory_attributes RP { $3 , List.rev $4 }
;

theory_attributes:
| theory_attribute { [$1] }
| theory_attributes theory_attribute { $2::$1 }
;

theory_attribute:
| SORTS_ATRB LP ids RP { Tsorts $3 }
| FUNS_ATRB LP fun_decls RP { Funs $3 }
| PREDS_ATRB LP pred_decls RP { Preds $3 }
| DEFINITION_ATRB STRING { Definition $2 }
| AXIOMS_ATRB LP formulas RP { Axioms $3 }
| NOTES_ATRB STRING { Tcomment }
| annot { Tcomment }
;

logic:
| LP LOGIC ID logic_attributes RP { $3 , List.rev $4 }
;

logic_attributes:
| logic_attribute { [$1] }
| logic_attributes logic_attribute { $2::$1 }
;

logic_attribute:
| THEORY_ATRB ID { Ltheory $2 }
| LANGUAGE_ATRB STRING { Lcomment }
| EXTENSIONS_ATRB STRING { Lcomment }
| NOTES_ATRB STRING { Lcomment }
| annot { Lcomment }
;

benchmark:
| LP BENCHMARK ID bench_attributes RP { $3 , List.rev $4 , !status}
;

bench_attributes:
| bench_attribute { [$1] }
| bench_attributes NOTES_ATRB STRING {$1}
| bench_attributes bench_attribute  { $2::$1 }
;

bench_attribute:
| LOGIC_ATRB ID                    { Pblogic $2 } 
| ASSUMPTION_ATRB formula          { Pbassumption (loc (), $2) }
| FORMULA_ATRB formula             { Pbformula (loc (), $2) }
| STATUS_ATRB status               { status:=$2;Pbstatus $2 }
| EXTRASORTS_ATRB LP ids RP        { Pbextr_sorts (List.rev $3) }
| EXTRAFUNS_ATRB LP fun_decls RP   { Pbextr_funs (List.rev $3) }
| EXTRAPREDS_ATRB LP pred_decls RP { Pbextr_preds (List.rev $3) }
| REWRITING_ATRB formulas          { Pbrewriting (loc (), $2) }
| annot                            { Pannotation }
;  

status:
| SAT     { Sat }
| UNSAT   { Unsat }
| UNKNOWN { Unknown }
;

symb:
| ID      { $1 }
| ARSYMB  { $1 }

fun_decls:
| fun_decls fun_decl { $2::$1 }
| fun_decl { [$1] }
;

fun_decl:
| LP symb ids opt_annots RP 
    { match $3 with 
	  r::l -> (loc (), {fname=$2; fargs=List.rev l; fres=r } )
	| [] -> assert false }
| LP NUMERAL ID opt_annots RP { (loc (), {fname=$2; fargs=[]; fres=(loc (), $3) } ) }
;  

pred_decls:
| pred_decls pred_decl { $2::$1 }
| pred_decl { [$1] }
;

pred_decl:
| LP symb opt_ids opt_annots RP  { (loc (), {pname=$2; pargs=List.rev $3}) }
;  

opt_ids:
| /* epsilon */ { [] }
| ids           { $1 }
;

ids:
| ID        { [(loc (),$1)] }
| ids ID { (loc (),$2)::$1 }
;

formulas:
| formula { [$1] }
| formula formulas { $1::$2 }
;

formula:
| TRUE                                                
   { mk_form True }
| LP TRUE annots RP                                   
   { mk_form True }
| FALSE                                               
   { mk_form False }
| LP FALSE annots RP                                  
   { mk_form False }
| FVAR                                                
   { mk_form (Fvar $1) }
| LP FVAR annots RP                                   
   { mk_form (Fvar $2) }
| ID                                                  
   { mk_form (Pred($1,[]) )}
| LP symb terms opt_annots RP                         
   { mk_form (Pred($2,List.rev $3)) }
| LP DISTINCT terms opt_annots RP                     
   { mk_form (Distinct (List.rev $3))}
| LP EQUALS terms opt_annots RP                       
   { mk_form (Equals (List.rev $3))}
| LP NOT formula opt_annots RP                        
   { mk_form (Not $3) }
| LP IMPLIES formula formula opt_annots RP            
   { mk_form (Implies($3,$4)) }
| LP IFTHENELSE formula formula formula opt_annots RP 
   { mk_form (Fite($3,$4,$5)) }
| LP AND formulas opt_annots RP                       
   { mk_form (And $3) }
| LP OR  formulas opt_annots RP                       
   { mk_form (Or $3) }
| LP XOR formulas opt_annots RP                       
   { mk_form (Xor $3) }
| LP IFF formulas opt_annots RP                       
   { mk_form (Iff $3) }
| LP FORALL binders formula opt_annots RP          
   { mk_form (Forall(List.rev $3,$4)) }
| LP EXISTS binders formula opt_annots RP          
   { mk_form (Exists(List.rev $3,$4)) }
| LP LET LP VAR term RP formula opt_annots RP      
   { mk_form (Let($4,mk_term $5,$7)) }
| LP FLET LP FVAR formula RP formula opt_annots RP 
   { mk_form (Flet($4,$5,$7)) }
;

opt_annots:
| /* epsilon */ {  }
| annots   {  }
;

annots:
| annot {}
| annots annot {}
;

annot:
| ATTRIBUTE            { }
| ATTRIBUTE USER_VALUE { }
;

binders:
| binder         { [$1] }
| binders binder { $2::$1 }
;

binder:
| LP VAR ID RP   { { var=$2 ; sort=$3 } }
;

terms:
| term       { [mk_term $1] }
| terms term { (mk_term $2)::$1 }

term:
| baseterm  { $1 }
| LP baseterm annots RP { $2 }
| LP ID terms opt_annots RP { Fun($2,List.rev $3) }
| LP VAR terms opt_annots RP { Fun($2,List.rev $3) }
| LP ARSYMB terms opt_annots RP { Fun($2,List.rev $3) }
| LP ITE formula term term opt_annots RP { Ite($3,mk_term $4,mk_term $5) }
;

baseterm:
| VAR { Var $1 }
| ID  { Fun($1,[]) }
| NUMERAL { Num $1 }
| RATIONAL { Rat $1 }
;
