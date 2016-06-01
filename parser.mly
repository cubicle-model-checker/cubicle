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
  open Util
  
  let _ = Smt.set_cc false; Smt.set_arith false; Smt.set_sum false


  (* Helper functions for location info *)

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)

  module S = Set.Make(Hstring)
    
  type t = 
    | Assign of (hstr_info * pglob_update * info)
    | Nondet of (hstr_info * info)
    | Upd of (pupdate * info)


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

  let get_id = 
    let cpt = ref 0 in 
    fun () -> incr cpt; !cpt 

  let get_info () = 
    { loc = loc (); active = true; id = get_id ()} 

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
%token <Num.num> REAL
%token <Num.num> INT
%token PLUS MINUS TIMES
%token IF THEN ELSE NOT
%token TRUE FALSE
%token UNDERSCORE AFFECT
%token EOF

%nonassoc prec_forall prec_exists
 %right IMP EQUIV  
%right OR
%right AND
%nonassoc prec_ite
/* %left prec_relation EQ NEQ LT LE GT GE */
/* %left PLUS MINUS */
%nonassoc NOT
/* %left BAR */

%type <Ptree.psystem> system
%start system
%%

system:
size_proc
type_defs
symbold_decls
decl_list
EOF
{ let ptype_defs = $2 in
  let pconsts, pglobals, parrays = $3 in
  psystem_of_decls ~pglobals ~pconsts ~parrays ~ptype_defs $4
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
    let l = $2 in add_fun_def l.hstr $4 $7
  }
;
var_decl:
  | VAR mident COLON lident {
    let l = $4 in
    let m = $2 in 
    if Hstring.equal l.hstr hint || Hstring.equal l.hstr hreal then Smt.set_arith true;
    Globals.add m.hstr;  
    get_info (), m , l }
;

const_decl:
  | CONST mident COLON lident {
    let l = $4 in 
    let m = $2 in 
    if Hstring.equal l.hstr hint || Hstring.equal l.hstr hreal then Smt.set_arith true;
    Consts.add m.hstr;
    get_info (),  m,  l}
;

array_decl:
  | ARRAY mident LEFTSQ lident_list_plus RIGHTSQ COLON lident { 
    let m = $2 in 
    if not (List.for_all (fun (p) -> Hstring.equal p.hstr hproc) $4) then
          raise Parsing.Parse_error;
    let l = $7 in     
    if Hstring.equal l.hstr hint || Hstring.equal l.hstr hreal then Smt.set_arith true;
	Arrays.add m.hstr;
	get_info (),  
m , ($4, l) }
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
  | TYPE lident {( get_info (), ($2, [])) }
  | TYPE lident EQ constructors 
      { Smt.set_sum true; List.iter (fun x -> Constructors.add x.hstr) $4; (get_info (), ($2, $4)) }
  | TYPE lident EQ BAR constructors 
      {  Smt.set_sum true; List.iter (fun x -> Constructors.add x.hstr) $5; (get_info (), ($2, $5)) }
;

constructors:
  | mident { [$1] }
  | mident BAR constructors { $1::$3 }
;

init:
  | INIT LEFTBR expr RIGHTBR {get_info (), [], $3} 
  | INIT LEFTPAR lidents RIGHTPAR LEFTBR expr RIGHTBR { get_info (), $3, $6 }
;

invariant:
  | INVARIANT LEFTBR expr RIGHTBR { get_info (), [], $3 }
  | INVARIANT LEFTPAR lidents RIGHTPAR LEFTBR expr RIGHTBR {get_info (), $3, $6 }
;

unsafe:
  | UNSAFE LEFTBR expr RIGHTBR { get_info () , [], $3 }
  | UNSAFE LEFTPAR lidents RIGHTPAR LEFTBR expr RIGHTBR { get_info (), $3, $6 }
;

transition_name:
  | lident { $1 }
  | mident { $1 }

transition:
  | TRANSITION transition_name LEFTPAR lidents RIGHTPAR 
      require
      LEFTBR assigns_nondets_updates RIGHTBR
      { let assigns, nondets, upds, inf = $8 in
	  { ptr_name = $2;
            ptr_args = $4; 
	    ptr_reqs = $6;
	    ptr_s = { 
              ptr_assigns = assigns; 
	      ptr_nondets = nondets; 
	      ptr_upds = upds;
              ptr_i = inf };
            ptr_loc = get_info ();
          }
      }
;

assigns_nondets_updates:
  |  { [], [], {t_pup_l = [] ; t_pup_i = get_info() } , get_info()}
  | assign_nondet_update 
      {  
	match $1 with
	  | Assign (x, y, inf) -> [{ a_n = x; a_p = y; a_i = inf}], [] , {t_pup_l = [] ; t_pup_i = get_info()}, get_info()
	  | Nondet (x, inf) -> [], [{n_n = x; n_i = inf}], {t_pup_l = [] ; t_pup_i = get_info()}, get_info()
	  | Upd (x, inf) -> [], [], {t_pup_l = [x] ; t_pup_i = inf}, get_info()
      }
  | assign_nondet_update PV assigns_nondets_updates 
      { 
	let assigns, nondets, upds, inf = $3 in
	match $1 with
	  | Assign (x, y, inf) -> ({a_n = x; a_p = y; a_i = inf}) :: assigns, nondets, upds, get_info()
	  | Nondet (x, inf) -> assigns, ({n_n = x; n_i = inf}) :: nondets, upds, get_info ()
	  | Upd (x, inf) -> assigns, nondets, { t_pup_l = x :: upds.t_pup_l ; t_pup_i = inf}, get_info ()
      }
;

assign_nondet_update:
  | assignment { $1 }
  | nondet { $1 }
  | update { $1 }
;

assignment:
  | mident AFFECT term { Assign ($1 , PUTerm $3, get_info ()) }
  | mident AFFECT CASE switchs { Assign ( $1 , PUCase ($4), get_info ()) }
;

nondet:
  | mident AFFECT DOT { Nondet ( $1 , get_info ()) }
  | mident AFFECT QMARK { Nondet ($1 , get_info ()) }
;

require:
  | { {r_f = PAtom (AAtom (Atom.True, get_info ())); r_i =  get_info ()} }
  | REQUIRE LEFTBR expr RIGHTBR { { r_f = $3 ; r_i = get_info ()} }
;

underscore:
  |UNDERSCORE {PAtom (AAtom (Atom.True, get_info()))}
;

switchs:
  | BAR underscore COLON term { 
    let (ter,i) = $4 in 
([{pup_form = $2 ; pup_t = ter; pup_i = get_info()}], get_info()) }
  | BAR switch { ([$2], get_info()) }
  | BAR switch switchs { let (l,_) = $3 in  (($2::l), get_info()) }
;

switch:
  | expr COLON term { let (p,_) = $3 in {pup_form = $1; pup_t =  p; pup_i =  get_info()} }
;


constnum:
  | REAL { ConstReal $1 }
  | INT { ConstInt $1 }
;

var_term:
  | mident {
    let l = $1 in 
    if Consts.mem l.hstr then Const (MConst.add (ConstName l.hstr) 1 MConst.empty)
      else Elem (l.hstr, sort l.hstr) }
  | proc_name { let l = $1 in Elem (l.hstr, Var) }
;

top_id_term:
  | var_term { match $1 with
      | Elem (v, Var) -> TVar ({ hstr = v; hstr_i = get_info()}, get_info())
      | _ -> TTerm ($1, get_info()) }
;


array_term:
  | mident LEFTSQ proc_name_list_plus RIGHTSQ {
    let l = $1 in 
    let new_l = List.map (fun x -> x.hstr) $3
    in  (Access (l.hstr, new_l))
  }
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
      { let l = $3 in Arith($1, MConst.add (ConstName l.hstr) 1 MConst.empty) }
  | var_or_array_term PLUS INT TIMES mident
      { let l = $5 in Arith($1, MConst.add (ConstName l.hstr) (Num.int_of_num $3) MConst.empty) }
  | var_or_array_term PLUS mident TIMES INT
      { let l = $3 in Arith($1, MConst.add (ConstName l.hstr) (Num.int_of_num $5) MConst.empty) }
  | var_or_array_term MINUS mident 
      { let l = $3 in Arith($1, MConst.add (ConstName l.hstr) (-1) MConst.empty) }
  | var_or_array_term MINUS INT TIMES mident 
      { let l = $5 in Arith($1, MConst.add (ConstName l.hstr) (- (Num.int_of_num $3)) MConst.empty) }
  | var_or_array_term MINUS mident TIMES INT 
      { let l = $3 in Arith($1, MConst.add (ConstName l.hstr) (- (Num.int_of_num $5)) MConst.empty) }
  | INT TIMES mident 
      { let l = $3 in Const(MConst.add (ConstName l.hstr) (Num.int_of_num $1) MConst.empty) }
  | MINUS INT TIMES mident 
      { let l = $4 in Const(MConst.add (ConstName l.hstr) (- (Num.int_of_num $2)) MConst.empty) }
  | constnum { Const (MConst.add $1 1 MConst.empty) }
;

term:
  | top_id_term { ($1, get_info()) } 
  | array_term { (TTerm ($1, get_info()), get_info()) }
  | arith_term { Smt.set_arith true; (TTerm ($1, get_info()), get_info()) }
;

lident:
  | LIDENT { { hstr = Hstring.make $1; hstr_i =  get_info() } }
;

const_proc:
  | CONSTPROC { { hstr = Hstring.make $1; hstr_i = get_info() }}
;

proc_name:
  | lident { $1 }
  | const_proc { $1 }
;

proc_name_list_plus:
  | proc_name { let p = $1 in [ p ]  }
  | proc_name COMMA proc_name_list_plus { let p = $1 in ( p )::$3 }
;

mident:
  | MIDENT { { hstr = Hstring.make $1 ; hstr_i = get_info() }}
;

lidents_plus:
  | lident {[ $1 ] }
  | lident lidents_plus { ( $1 )::$2 }
;

lidents:
  | { [] }
  | lidents_plus { $1 }
;

lident_list_plus:
  | lident { [ $1 ] }
  | lident COMMA lident_list_plus { ( $1 )::$3 }
;

lident_comma_list:
  | { [] }
  | lident_list_plus { let new_l = List.map (fun x -> x.hstr) $1  in new_l}
;

lidents_plus_distinct:
  | lident { let l = $1 in  [ l ] }
  | lident NEQ lidents_plus_distinct {let l = $1 in ( l ) :: $3 }
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
  | TRUE { AAtom (Atom.True, get_info()) }
  | FALSE { AAtom (Atom.False, get_info()) }
  /* | lident { AVar $1 } RR conflict with proc_name */
  | term EQ term { let (t1,_) = $1 in let (t3,_) = $3 in AEq (t1, t3, get_info()) }
  | term NEQ term { let (t1,_) = $1 in let (t3,_) = $3 in ANeq (t1, t3, get_info()) }
  | term LT term { let (t1,_) = $1 in 
                   let (t3,_) = $3 in 
                   Smt.set_arith true; 
                   ALt (t1, t3, get_info()) }
  | term LE term {let (t1,_) = $1 in let (t3,_) = $3 in  Smt.set_arith true; ALe (t1, t3, get_info()) }
  | term GT term { let (t1,_) = $1 in let (t3,_) = $3 in Smt.set_arith true; ALt (t3, t1, get_info()) }
  | term GE term { let (t1,_) = $1 in let (t3,_) = $3 in Smt.set_arith true; ALe (t3, t1, get_info()) }
;

neg: 
  |NOT { get_info()}
;

expr:
  | simple_expr { $1 }
  | neg expr { PNot ($1, $2, get_info()) }
  | expr AND expr { PAnd ([$1; $3], get_info()) }
  | expr OR expr  { POr ([$1 ; $3], get_info()) }
  | expr IMP expr { PImp ($1, $3, get_info()) }
  | expr EQUIV expr { PEquiv ($1, $3, get_info()) }
  | IF expr THEN expr ELSE expr %prec prec_ite { PIte ($2, $4, $6, get_info()) }
  | FORALL lidents_plus_distinct DOT expr %prec prec_forall { PForall ($2, $4, get_info())  }
  | EXISTS lidents_plus_distinct DOT expr %prec prec_exists { PExists ($2, $4, get_info()) }
  | FORALL_OTHER lident DOT expr %prec prec_forall {
    PForall_other ([$2], $4, get_info()) }
  | EXISTS_OTHER lident DOT expr %prec prec_exists {
    PExists_other ([$2], $4, get_info()) }
;

simple_expr:
  | literal { PAtom ($1) }
  | LEFTPAR expr RIGHTPAR { $2 }
  | lident LEFTPAR expr_or_term_comma_list RIGHTPAR { let l = $1 in app_fun l.hstr $3 }
;



expr_or_term_comma_list:
  | { [] }
  | term  { let (t,_) = $1 in [PT t] }
  | expr  { [PF $1] }
  | term COMMA expr_or_term_comma_list { let (t,_) = $1 in PT t :: $3 }
  | expr COMMA expr_or_term_comma_list { PF $1 :: $3 }
;


update:
  | mident LEFTSQ proc_name_list_plus RIGHTSQ AFFECT CASE switchs
      { List.iter (fun (p) ->
          if (Hstring.view p.hstr).[0] = '#' then
            raise Parsing.Parse_error;
        ) $3;
        Upd 
          ({ pup_loc = get_info () ; pup_arr = $1 ; pup_arg = $3; pup_swts = $7; pup_info = None}, get_info())}
  | mident LEFTSQ proc_name_list_plus RIGHTSQ AFFECT term
      { let l = $1 in 
        let (t,i) = $6 in 
        let cube, rjs =
          List.fold_left (fun (cube, rjs) i ->
            let j = { hstr = fresh_var (); hstr_i = i.hstr_i} in
            let c = PAtom (AEq (TVar (j, get_info()), TVar (i, get_info()),get_info())) in
            c :: cube, j :: rjs) ([], []) $3 in
        let a = PAnd (cube, get_info()) in
        let js = List.rev rjs in
        let new_l = List.map (fun x -> x.hstr) js in 
	let sw = [
          { pup_form = a; pup_t =  t; pup_i =  get_info()};
          { pup_form = PAtom ((AAtom (Atom.True, get_info()))); pup_t =  TTerm ((Access(l.hstr, new_l)), i);
 pup_i =  get_info()}] in
	Upd ({ pup_loc = get_info (); pup_arr = $1; pup_arg = js; pup_swts = (sw, i); pup_info = Some (l.hstr,$3,t)}, get_info())}
;
