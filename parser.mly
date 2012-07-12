/**************************************************************************/
/*                                                                        */
/*                                  Cubicle                               */
/*             Combining model checking algorithms and SMT solvers        */
/*                                                                        */
/*                  Sylvain Conchon and Alain Mebsout                     */
/*                  Universite Paris-Sud 11                               */
/*                                                                        */
/*  Copyright 2011. This file is distributed under the terms of the       */
/*  Apache Software License version 2.0                                   */
/*                                                                        */
/**************************************************************************/

%{

  open Ast
  open Parsing
  open Atom

  type t = 
    | Assign of Hstring.t * term
    | Nondet of Hstring.t
    | Upd of update

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
    else if Arrays.mem s then Arr
    else Var

  let hproc = Hstring.make "proc"

  let set_from_list = List.fold_left (fun sa a -> add a sa) SAtom.empty 

  let fresh_var = 
    let cpt = ref 0 in
    fun () -> incr cpt; Hstring.make ("_j"^(string_of_int !cpt))

%}

%token VAR ARRAY CONST TYPE INIT TRANSITION INVARIANT CASE FORALL
%token ASSIGN UGUARD REQUIRE NEQ UNSAFE FORWARD
%token OR AND COMMA PV DOT
%token <string> LIDENT
%token <string> MIDENT
%token LEFTPAR RIGHTPAR COLON EQ NEQ LT LE LEFTSQ RIGHTSQ LEFTBR RIGHTBR BAR 
%token <Num.num> REAL
%token <Num.num> INT
%token PLUS MINUS
%token UNDERSCORE AFFECT
%token EOF

%left PLUS MINUS
%right OR
%right AND
%nonassoc for_all
%left BAR

%type <Ast.system> system
%start system
%%

system:
type_defs
declarations
init
invariants
unsafe_list
forward_list
transitions 
{ let consts, vars, arrays = $2 in
  { type_defs = $1; 
    consts = consts; 
    globals = vars;
    arrays = arrays; 
    init = $3; 
    invs = $4;
    unsafe = $5; 
    forward = $6;
    trans = $7 } }
;

declarations :
  | { [], [], [] }
  | const_decl declarations 
      { let consts, vars, arrays = $2 in ($1::consts), vars, arrays }
  | var_decl declarations 
      { let consts, vars, arrays = $2 in consts, ($1::vars), arrays }
  | array_decl declarations 
      { let consts, vars, arrays = $2 in consts, vars, ($1::arrays) }
;

var_decl:
  | VAR mident COLON lident { Globals.add $2; $2, $4 }
;

const_decl:
  | CONST mident COLON lident { Consts.add $2; $2, $4 }
;

array_decl:
| ARRAY mident LEFTSQ lident RIGHTSQ COLON lident 
   { if Hstring.compare $4 hproc <> 0 then raise Parsing.Parse_error;
     Arrays.add $2; 
     $2, ($4, $7)}
;

type_defs:
| { [] }
| type_def_plus { $1 }
;

type_def_plus:
| type_def { [$1] }
| type_def type_def_plus { $1::$2 }
;

type_def:
| TYPE lident { ($2, []) }
| TYPE lident EQ constructors 
     { List.iter Constructors.add $4; ($2, $4) }
| TYPE lident EQ BAR constructors 
     { List.iter Constructors.add $5; ($2, $5) }
;

constructors:
| mident { [$1] }
| mident BAR constructors { $1::$3 }
;

init:
INIT LEFTPAR lident_option RIGHTPAR LEFTBR cube RIGHTBR 
{ $3, $6 }
;

invariants:
| { [] }
| invariant invariants { $1 :: $2 }
;

invariant:
| INVARIANT LEFTPAR lident_plus RIGHTPAR LEFTBR cube RIGHTBR { $3, $6 }
;

unsafe:
UNSAFE LEFTPAR lidents RIGHTPAR LEFTBR cube RIGHTBR 
{ $3, $6 }
;

unsafe_list:
| unsafe { [$1] }
| unsafe unsafe_list { $1::$2 }
;

forward:
FORWARD LEFTPAR lidents COMMA lidents RIGHTPAR LEFTBR cube RIGHTBR 
{ $3, $5, $8 }
;

forward_list:
| { [] }
| forward forward_list { $1::$2 }
;

transitions:
| { [] }
| transitions_list { $1 }
;

transitions_list:
| transition { [$1] }
| transition transitions_list { $1::$2 }
;

transition:
TRANSITION lident LEFTPAR lident_plus RIGHTPAR 
require
LEFTBR assigns_nondets_updates RIGHTBR
{ let reqs, ureq = $6 in
  let assigns, nondets, upds = $8 in
  { tr_name = $2; tr_args = $4; 
    tr_reqs = reqs; tr_ureq = ureq; 
    tr_assigns = assigns; 
    tr_nondets = nondets; 
    tr_upds = upds } 
}
;

assigns_nondets_updates:
|  { [], [], [] }
| assign_nondet_update 
    {  
      match $1 with
	| Assign (x, y) -> [x, y], [], []
	| Nondet x -> [], [x], []
	| Upd x -> [], [], [x]
    }
| assign_nondet_update PV assigns_nondets_updates 
       { 
	 let assigns, nondets, upds = $3 in
	 match $1 with
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
| mident AFFECT term    { Assign ($1, $3) }
;

nondet:
| mident AFFECT DOT    { Nondet $1 }
;

require:
| { SAtom.empty, [] }
| REQUIRE LEFTBR ucube RIGHTBR { $3 }
;

update:
| mident LEFTSQ lident RIGHTSQ AFFECT CASE switchs
    { Upd { up_arr = $1; up_arg = $3; up_swts = $7} }
| mident LEFTSQ lident RIGHTSQ AFFECT term
    { let j = fresh_var () in
      let cube = 
	SAtom.singleton (Comp(Elem (j, Var), Eq, Elem ($3, Var))) in
      let sw = [(cube, $6); (SAtom.empty, Access($1, j, Var))] in
      Upd { up_arr = $1; up_arg = j; up_swts = sw}  }
;

switchs:
| BAR UNDERSCORE COLON term { [(SAtom.empty, $4)] }
| BAR switch { [$2] }
| BAR switch switchs { $2::$3 }
;

switch:
cube COLON term { $1, $3 }
;

ucube:
| literal { SAtom.singleton $1, [] }
| uliteral { SAtom.empty, [$1] }
| literal AND ucube { let s, l = $3 in SAtom.add $1 s, l }
| uliteral AND ucube { let s, l = $3 in s, $1::l }
;

cube:
| literal { SAtom.singleton $1 }
| literal AND cube { SAtom.add $1 $3 }
;

uliteral:
| FORALL lident DOT literal { $2, [SAtom.singleton $4] }
| FORALL lident DOT LEFTPAR dnf RIGHTPAR { $2, $5 }
;


dnf:
| cube { [$1] }
| cube OR dnf {$1 :: $3}
;

literal:
| term operator term { Comp($1, $2, $3) }
;

constnum:
| REAL { ConstReal $1 }
| INT { ConstInt $1 }
;

var_term:
| mident { 
    if Consts.mem $1 then Const (MConst.add (ConstName $1) 1 MConst.empty)
    else Elem ($1, sort $1) }
| lident { Elem ($1, Var) }
;

array_term:
| mident LEFTSQ lident RIGHTSQ { Access($1,$3, Var) }
| mident LEFTSQ mident RIGHTSQ { Access($1,$3, sort $3) }
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
| var_or_array_term MINUS mident 
    { Arith($1, MConst.add (ConstName $3) (-1) MConst.empty) }
| constnum { Const (MConst.add $1 1 MConst.empty) }
;

term:
| var_or_array_term { $1 }
| arith_term { $1 }
;

mident:
| MIDENT { Hstring.make $1 }
;

lident_plus:
|  { [] }
| lidents { $1 }
;

lidents:
| lident        { [$1] }
| lident lidents { $1::$2 }
;

lident_option:
| { None }
| LIDENT { Some (Hstring.make $1) }
;

lident:
| LIDENT { Hstring.make $1 }
;

operator:
| EQ { Eq }
| NEQ { Neq }
| LT { Lt }
| LE { Le }
