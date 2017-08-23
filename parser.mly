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
  open Weakparse
  
  let _ = Smt.set_cc false; Smt.set_arith false; Smt.set_sum false


  (* Helper functions for location info *)

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)


  type t = 
    | Assign of Hstring.t * pglob_update
    | Nondet of Hstring.t
    | Upd of pupdate
    | Write of Variable.t option * Hstring.t * Variable.t list * pglob_update

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

  module Weaks = struct
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
%token EOF
%token FENCE WEAK AT

%nonassoc IN       
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
type_defs
symbold_decls
decl_list
EOF
{ let ptype_defs = $2 in
  Smt.set_sum true;
  let b = [Hstring.make "@MTrue"; Hstring.make "@MFalse"] in
  List.iter Constructors.add b;
  let ptype_defs = (loc (), (Hstring.make "mbool", b)) :: ptype_defs in
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
  | init { let l, p, e = $1 in PInit (l, p, fix_rd_init e) }
  | invariant { let l, n, p, e = $1 in PInv (l, n, p, fix_rd_expr None e) }
  | unsafe { let l, n, p, e = $1 in PUnsafe (l, n, p, fix_rd_expr None e) }
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

weak_opt:
  | /*epsilon*/ { false }
  | WEAK { true }

var_decl:
  | weak_opt VAR mident COLON lident {
    if Hstring.equal $5 hint || Hstring.equal $5 hreal then Smt.set_arith true;
    Globals.add $3; if $1 then Weaks.add $3;
    loc (), $3, $5, $1 }
;

const_decl:
  | CONST mident COLON lident { 
    if Hstring.equal $4 hint || Hstring.equal $4 hreal then Smt.set_arith true;
    Consts.add $2;
    loc (), $2, $4 }
;

array_decl:
  | weak_opt ARRAY mident LEFTSQ lident_list_plus RIGHTSQ COLON lident {
        if not (List.for_all (fun p -> Hstring.equal p hproc) $5) then
	  raise Parsing.Parse_error;
	if Hstring.equal $8 hint || Hstring.equal $8 hreal then Smt.set_arith true;
	Arrays.add $3; if $1 then Weaks.add $3;
	loc (), $3, ($5, $8), $1 }
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
  | INVARIANT name_opt LEFTBR expr RIGHTBR { loc (), $2, [], $4 }
  | INVARIANT name_opt LEFTPAR lidents RIGHTPAR LEFTBR expr RIGHTBR
        { loc (), $2, $4, $7 }
;

unsafe:
  | UNSAFE name_opt LEFTBR expr RIGHTBR { loc (), $2, [], $4 }
  | UNSAFE name_opt LEFTPAR lidents RIGHTPAR LEFTBR expr RIGHTBR
        { loc (), $2, $4, $7 }
;

name_opt:
  | /*epsilon*/     { None }
  | transition_name { Some $1 }

transition_name:
  | lident {$1}
  | mident {$1}

transition:
  | TRANSITION transition_name LEFTPAR lidents_thr RIGHTPAR
      require
      LEFTBR let_assigns_nondets_updates RIGHTBR
      { let lets, (assigns, nondets, upds, writes) = $8 in
	{   ptr_lets = lets;
	    ptr_name = $2;
            ptr_args = fst $4;
	    ptr_reqs = fix_rd_expr (snd $4) $6;
	    ptr_assigns = List.map (fix_rd_assign (snd $4)) assigns;
	    ptr_nondets = nondets; 
	    ptr_upds = List.map (fix_rd_upd (snd $4)) upds;
            ptr_loc = loc ();
	    ptr_writes = List.map (fix_rd_write (snd $4)) writes;
	    ptr_fence = None;
          }
      }
;

let_assigns_nondets_updates:
  | assigns_nondets_updates { [], $1 }
  | LET lident EQ term IN let_assigns_nondets_updates {
	  let lets, l = $6 in
	  ($2, $4) :: lets, l}
;
  
assigns_nondets_updates:
  |  { [], [], [], [] }
  | assign_nondet_update 
      {  
	match $1 with
	  | Assign (x, y) -> [x, y], [], [], []
	  | Nondet x -> [], [x], [], []
	  | Upd x -> [], [], [x], []
	  | Write (x, y, z, t) -> [], [], [], [x, y, z, t]
      }
  | assign_nondet_update PV assigns_nondets_updates 
      { 
	let assigns, nondets, upds, writes = $3 in
	match $1 with
	  | Assign (x, y) -> (x, y) :: assigns, nondets, upds, writes
	  | Nondet x -> assigns, x :: nondets, upds, writes
	  | Upd x -> assigns, nondets, x :: upds, writes
	  | Write (x, y, z, t) -> assigns, nondets, upds, (x, y, z, t) :: writes
      }
;

assign_nondet_update:
  | assignment { $1 }
  | nondet { $1 }
  | update { $1 }
;

assignment:
  | assignment_weak { $1 }
  | proc_name AT assignment_weak {
      match $3 with
      | Write (_, var, args, upd) ->
         Write (Some $1, var, args, upd)
      | _ -> $3 }
;

assignment_weak:
  | assignment_base {
      match $1 with
      | Assign (var, upd) ->
         if Weaks.mem var then Write (None, var, [], upd)
         else $1
      | _ -> assert false }
;

assignment_base:
  | mident AFFECT term { Assign ($1, PUTerm $3) }
  | mident AFFECT CASE switchs { Assign ($1, PUCase $4) }
;

nondet:
  | mident AFFECT DOT { Nondet $1 }
  | mident AFFECT QMARK { Nondet $1 }
;

require:
  | { PAtom (AAtom (Atom.True)) }
  | REQUIRE LEFTBR expr RIGHTBR { $3 }
;

update:
  | update_weak { $1 }
  | proc_name AT update_weak {
      match $3 with
      | Write (_, var, args, upd) ->
         Write (Some $1, var, args, upd)
      | _ -> $3 }
;

update_weak:
  | mident LEFTSQ proc_name_list_plus RIGHTSQ AFFECT CASE switchs
    { if Weaks.mem $1 then Write (None, $1, $3, PUCase $7)
      else begin
        List.iter (fun p ->
          if (Hstring.view p).[0] = '#' then
            raise Parsing.Parse_error;
        ) $3;
        Upd { pup_loc = loc (); pup_arr = $1; pup_arg = $3; pup_swts = $7 }
      end }
  | mident LEFTSQ proc_name_list_plus RIGHTSQ AFFECT term
    { if Weaks.mem $1 then Write (None, $1, $3, PUTerm $6)
      else begin
        let cube, rjs =
          List.fold_left (fun (cube, rjs) i ->
            let j = fresh_var () in
            let c = PAtom (AEq (TVar j, TVar i)) in
            c :: cube, j :: rjs) ([], []) $3 in
        let a = PAnd cube in
        let js = List.rev rjs in
	let sw = [(a, $6); (PAtom (AAtom Atom.True), TTerm (Access($1, js)))] in
	Upd { pup_loc = loc (); pup_arr = $1; pup_arg = js; pup_swts = sw }
      end }
;

switchs:
  | BAR UNDERSCORE COLON term { [(PAtom (AAtom (Atom.True)), $4)] }
  | BAR switch { [$2] }
  | BAR switch switchs { $2::$3 }
;

switch:
  | expr COLON term { $1, $3 }
;


constnum:
  | REAL { ConstReal $1 }
  | INT { ConstInt $1 }
;

var_term:
  | mident { 
      if Weaks.mem $1 then Read(Hstring.make "", $1, []) else
      if Consts.mem $1 then Const (MConst.add (ConstName $1) 1 MConst.empty)
      else Elem ($1, sort $1) }
  | proc_name { Elem ($1, Var) }
  | proc_name AT mident {
      if Weaks.mem $3 then Read($1, $3, []) else
      if Consts.mem $3 then Const (MConst.add (ConstName $3) 1 MConst.empty)
      else Elem ($3, sort $3) }
;

top_id_term:
  | var_term { match $1 with
                 | Elem (v, Var) -> TVar v
                 | _ -> TTerm $1 }
;


array_term:
  | mident LEFTSQ proc_name_list_plus RIGHTSQ {
      if Weaks.mem $1 then Read(Hstring.make "", $1, $3)
      else Access ($1, $3) }
  | proc_name AT mident LEFTSQ proc_name_list_plus RIGHTSQ {
      if Weaks.mem $3 then Read($1, $3, $5)
      else Access ($3, $5) }
;

var_or_array_term:
  | var_term { $1 }
  | array_term { $1 }
;

arith_term:
  | var_or_array_term PLUS constnum 
      { Arith($1, MConst.add $3 1 MConst.empty) }
  | var_or_array_term MINUS constnum 
      { Arith($1, MConst.add $3 (-1) MConst.empty) }
  | var_or_array_term PLUS mident 
      { Arith($1, MConst.add (ConstName $3) 1 MConst.empty) }
  | var_or_array_term PLUS INT TIMES mident
      { Arith($1, MConst.add (ConstName $5) (Num.int_of_num $3) MConst.empty) }
  | var_or_array_term PLUS mident TIMES INT
      { Arith($1, MConst.add (ConstName $3) (Num.int_of_num $5) MConst.empty) }
  | var_or_array_term MINUS mident 
      { Arith($1, MConst.add (ConstName $3) (-1) MConst.empty) }
  | var_or_array_term MINUS INT TIMES mident 
      { Arith($1, MConst.add (ConstName $5) (- (Num.int_of_num $3)) MConst.empty) }
  | var_or_array_term MINUS mident TIMES INT 
      { Arith($1, MConst.add (ConstName $3) (- (Num.int_of_num $5)) MConst.empty) }
  | INT TIMES mident 
      { Const(MConst.add (ConstName $3) (Num.int_of_num $1) MConst.empty) }
  | MINUS INT TIMES mident 
      { Const(MConst.add (ConstName $4) (- (Num.int_of_num $2)) MConst.empty) }
  | constnum { Const (MConst.add $1 1 MConst.empty) }
;

term:
  | top_id_term { $1 } 
  | array_term { TTerm $1 }
  | arith_term { Smt.set_arith true; TTerm $1 }
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

lidents_thr_plus:
  | lident { [$1], None }
  | lident lidents_thr_plus { $1::(fst $2), (snd $2) }
  | LEFTSQ lident RIGHTSQ { [$2], Some $2 }
  | LEFTSQ lident RIGHTSQ lidents_plus { $2::$4, Some $2 }
;

lidents_thr:
  | { [], None }
  | lidents_thr_plus { $1 }

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
  | FENCE LEFTPAR proc_name RIGHTPAR { AEq (TTerm (Fence $3), TTerm (Elem (Term.htrue, Constr))) }
  /* | lident { AVar $1 } RR conflict with proc_name */
  | term EQ term { AEq ($1, $3) }
  | term NEQ term { ANeq ($1, $3) }
  | term LT term { Smt.set_arith true; ALt ($1, $3) }
  | term LE term { Smt.set_arith true; ALe ($1, $3) }
  | term GT term { Smt.set_arith true; ALt ($3, $1) }
  | term GE term { Smt.set_arith true; ALe ($3, $1) }
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
  | term  { [PT $1] }
  | expr  { [PF $1] }
  | term COMMA expr_or_term_comma_list { PT $1 :: $3 }
  | expr COMMA expr_or_term_comma_list { PF $1 :: $3 }
;
