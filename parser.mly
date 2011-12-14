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

  let sort s = 
    if Constructors.mem s then Constr 
    else if Globals.mem s then Glob
    else if Arrays.mem s then Arr
    else Var

  let hproc = Hstring.make "proc"

  let set_from_list = List.fold_left (fun sa a -> add a sa) SAtom.empty 

  let rec extract_underscore = function
    | [] -> assert false
    | (s, t) :: l when SAtom.is_empty s -> List.rev l, t
    | _ -> raise Parsing.Parse_error 

%}

%token GLOBALS ARRAYS TYPE INIT TRANSITION INVARIANT
%token ASSIGN UGUARD REQUIRE NEQ UNSAFE
%token OR AND COMMA PV DOT
%token <string> LIDENT
%token <string> MIDENT
%token LEFTPAR RIGHTPAR COLON EQ NEQ LT LE LEFTSQ RIGHTSQ LEFTBR RIGHTBR BAR 
%token <int> INT
%token PLUS MINUS
%token UNDERSCORE AFFECT
%token EOF

%left PLUS MINUS
%right OR
%right AND
%left BAR

%type <Ast.system> system
%start system
%%

system:
type_defs
global_defs
array_defs
init
invariants
unsafe
transitions 
{ { type_defs = $1; 
    globals = $2;
    arrays = $3; 
    init = $4; 
    invs = $5;
    unsafe = $6; 
    trans = $7 } }
;

global_defs:
| { [] }
| GLOBALS EQ globals { List.iter (fun (x,_) -> Globals.add x) $3; $3 }
;

array_defs:
| { [] }
| ARRAYS EQ arrays { List.iter (fun (x,_) -> Arrays.add x) $3; $3 }
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
| TYPE lident EQ constructors { List.iter Constructors.add $4; ($2, $4) }
;

constructors:
| mident { [$1] }
| mident BAR constructors { $1::$3 }
;

globals:
| global { [$1] }
| global globals { $1::$2 }
;

global:
| mident LEFTSQ lident RIGHTSQ { $1, $3 }
;

arrays:
| array { [$1] }
| array arrays { $1::$2 }
;

array:
mident LEFTSQ lident COMMA lident RIGHTSQ 
  { if Hstring.compare $3 hproc <> 0 then raise Parsing.Parse_error;
    $1, ($3, $5) } 
;

init:
INIT LEFTPAR lident_option RIGHTPAR LEFTBR cubes RIGHTBR 
{ $3, $6 }
;

invariants:
| { [] }
| invariant invariants { $1 :: $2 }
;

invariant:
| INVARIANT LEFTPAR lidents RIGHTPAR LEFTBR cubes RIGHTBR { $3, $6 }
;


unsafe:
UNSAFE LEFTPAR lidents RIGHTPAR LEFTBR cubes RIGHTBR 
{ $3, $6 }
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
urequire
assigns
updates
{ let assigns, nondets = $8 in
  { tr_name = $2; tr_args = $4; 
    tr_reqs = $6; tr_ureq = $7; tr_assigns = assigns; 
    tr_nondets = nondets; tr_upds = $9 } }
;

assigns:
| { [], [] }
| ASSIGN LEFTBR assignments RIGHTBR { $3 }
;

assignments:
| assignment { [$1], [] }
| nondet { [], [$1] }
| assignment PV assignments { let l1, l2 = $3 in $1::l1, l2 }
| nondet PV assignments { let l1, l2 = $3 in l1, $1::l2 }
;

assignment:
| mident AFFECT term    { $1, $3 }
;

nondet:
| mident AFFECT DOT    { $1 }
;

require:
| { SAtom.empty }
| REQUIRE LEFTBR cubes RIGHTBR { $3 }
;

urequire:
| { None }
| UGUARD LEFTPAR lident RIGHTPAR LEFTBR cubes RIGHTBR { Some ($3,$6) }
;


updates:
| { [] }
| update_plus { $1 }
;

update_plus:
| update { [$1] }
| update update_plus { $1::$2 }
;

update:
mident LEFTSQ lident RIGHTSQ AFFECT LEFTBR switchs_underscore RIGHTBR
{ { up_arr = $1; up_arg = $3; up_swts = $7} }
;

switchs_underscore:
| switchs { extract_underscore (List.rev $1) }

switchs:
| BAR UNDERSCORE COLON term { [(SAtom.empty, $4)] }
| BAR switch { [$2] }
| BAR switch switchs { $2::$3 }
;

switch:
cubes COLON term { $1, $3 }
;

cubes:
| cube { SAtom.singleton $1 }
| cube AND cubes { SAtom.add $1 $3 }
;

cube:
| term operator term { Comp($1, $2, $3) }
;

term:
| mident { Elem ($1, sort $1) }
| lident { Elem ($1, Var) }
| mident LEFTSQ lident RIGHTSQ { Access($1,$3) }
| mident PLUS INT { Arith($1, sort $1, Plus, $3) }
| mident MINUS INT { Arith($1, sort $1, Minus, $3) }
| INT { Const $1 }
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
