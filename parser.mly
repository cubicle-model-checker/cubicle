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

  let _ = Smt.set_cc false; Smt.set_arith false; Smt.set_sum false

  type t = 
    | Assign of Hstring.t * Term.t
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

%}

%token VAR ARRAY CONST TYPE INIT TRANSITION INVARIANT CASE FORALL
%token SIZEPROC
%token ASSIGN UGUARD REQUIRE NEQ UNSAFE
%token OR AND COMMA PV DOT QMARK
%token <string> CONSTPROC
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
size_proc
type_defs
declarations
init
invariants
unsafe_list
transitions 
{ let consts, vars, arrays = $3 in
  { type_defs = $2; 
    consts = consts; 
    globals = vars;
    arrays = arrays; 
    init = $4; 
    invs = $5;
    unsafe = $6; 
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
  | VAR mident COLON lident { 
    if Hstring.equal $4 hint || Hstring.equal $4 hreal then Smt.set_arith true;
    Globals.add $2; 
    $2, $4 }
;

const_decl:
  | CONST mident COLON lident { 
    if Hstring.equal $4 hint || Hstring.equal $4 hreal then Smt.set_arith true;
    Consts.add $2;
    $2, $4 }
;

array_decl:
  | ARRAY mident LEFTSQ lident_list_plus RIGHTSQ COLON lident { 
        if not (List.for_all (fun p -> Hstring.equal p hproc) $4) then
          raise Parsing.Parse_error;
        if Hstring.equal $7 hint || Hstring.equal $7 hreal then Smt.set_arith true;
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

size_proc:
  | { () }
  | SIZEPROC INT { Options.size_proc := Num.int_of_num $2 }
;
      
type_def:
  | TYPE lident { ($2, []) }
  | TYPE lident EQ constructors 
      { Smt.set_sum true; List.iter Constructors.add $4; ($2, $4) }
  | TYPE lident EQ BAR constructors 
      { Smt.set_sum true; List.iter Constructors.add $5; ($2, $5) }
;

constructors:
  | mident { [$1] }
  | mident BAR constructors { $1::$3 }
;

init:
  | INIT LEFTPAR lidents RIGHTPAR LEFTBR dnf RIGHTBR 
      { $3, $6 }
;

invariants:
  | { [] }
  | invariant invariants { $1 :: $2 }
;

invariant:
  | INVARIANT LEFTPAR lidents RIGHTPAR LEFTBR cube RIGHTBR { $3, $6 }
;

unsafe:
  | UNSAFE LEFTPAR lidents RIGHTPAR LEFTBR cube RIGHTBR { $3, $6 }
;

unsafe_list:
  | unsafe { [$1] }
  | unsafe unsafe_list { $1::$2 }
;

transitions:
  | { [] }
  | transitions_list { $1 }
;

transitions_list:
  | transition { [$1] }
  | transition transitions_list { $1::$2 }
;

transition_name:
  | lident {$1}
  | mident {$1}

transition:
  | TRANSITION transition_name LEFTPAR lidents RIGHTPAR 
      require
      LEFTBR assigns_nondets_updates RIGHTBR
      { let reqs, ureq = $6 in
	let assigns, nondets, upds = $8 in
	{ tr_name = $2;
          tr_args = $4; 
	  tr_reqs = reqs;
          tr_ureq = ureq; 
	  tr_assigns = assigns; 
	  tr_nondets = nondets; 
	  tr_upds = upds;
          (* tr_tau = fun _ _ _ -> Atom.True; *)
        } 
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
  | mident AFFECT DOT { Nondet $1 }
  | mident AFFECT QMARK { Nondet $1 }
;

require:
  | { SAtom.empty, [] }
  | REQUIRE LEFTBR ucube RIGHTBR { $3 }
;

update:
  | mident LEFTSQ proc_name_list_plus RIGHTSQ AFFECT CASE switchs
      { List.iter (fun p ->
          if (Hstring.view p).[0] = '#' then
            raise Parsing.Parse_error;
        ) $3;
        Upd { up_arr = $1; up_arg = $3; up_swts = $7} }
  | mident LEFTSQ proc_name_list_plus RIGHTSQ AFFECT term
      { let cube, rjs =
          List.fold_left (fun (cube, rjs) i ->
            let j = fresh_var () in
            let c = Atom.Comp(Elem (j, Var), Eq, Elem (i, Var)) in
            SAtom.add c cube, j :: rjs) (SAtom.empty, []) $3 in
        let js = List.rev rjs in
	let sw = [(cube, $6); (SAtom.empty, Access($1, js))] in
	Upd { up_arr = $1; up_arg = js; up_swts = sw}  }
;

switchs:
  | BAR UNDERSCORE COLON term { [(SAtom.empty, $4)] }
  | BAR switch { [$2] }
  | BAR switch switchs { $2::$3 }
;

switch:
  | cube COLON term { $1, $3 }
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
  | term operator term { Atom.Comp($1, $2, $3) }
;

constnum:
  | REAL { ConstReal $1 }
  | INT { ConstInt $1 }
;

var_term:
  | mident { 
      if Consts.mem $1 then Const (MConst.add (ConstName $1) 1 MConst.empty)
      else Elem ($1, sort $1) }
  | proc_name { Elem ($1, Var) }
;


array_term:
  | mident LEFTSQ proc_name_list_plus RIGHTSQ {
    Access ($1, $3)
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
      { Arith($1, MConst.add (ConstName $3) 1 MConst.empty) }
  | var_or_array_term MINUS mident 
      { Arith($1, MConst.add (ConstName $3) (-1) MConst.empty) }
  | constnum { Const (MConst.add $1 1 MConst.empty) }
;

term:
  | var_or_array_term { $1 }
  | arith_term { Smt.set_arith true; $1 }
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

lidents:
  |  { [] }
  | lident lidents { $1::$2 }
;

lident_list_plus:
  | lident { [$1] }
  | lident COMMA lident_list_plus { $1::$3 }
;

operator:
  | EQ { Eq }
  | NEQ { Neq }
  | LT { Smt.set_arith true; Lt }
  | LE { Smt.set_arith true; Le }
