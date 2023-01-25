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
    | PLock of lock_uses
    | PUnlock of lock_uses
    | PWait of lock_uses
    | PNotify of lock_uses
    | PNotifyAll of lock_uses

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
%token <string*string> CONSTPROC
%token <string> LIDENT
%token <string> MIDENT
%token <string> SPROCS
%token ADDPROC SUBPROC COMPPROC
%token LEFTPAR RIGHTPAR COLON EQ NEQ LT LE GT GE
%token LEFTSQ RIGHTSQ LEFTBR RIGHTBR BAR
%token IN
%token LET
%token RELEASE RELEASELOCK RELEASERLOCK RELEASESEM RELEASECOND ACQUIRE ACQUIRELOCK ACQUIRERLOCK ACQUIRESEM ACQUIRECOND
%token WAIT NOTIFY NOTIFYALL KILLPROC GENPROC EXEC
%token <Num.num> REAL
%token <Num.num> INT
%token PLUS MINUS TIMES
%token IF THEN ELSE NOT
%token TRUE FALSE
%token UNDERSCORE AFFECT
%token STATUS HELP CLEAR RESTART TEST
%token EOF

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

%start toplevel     
%type <Ast.toplevel> toplevel
  
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

transition:
  | TRANSITION transition_name LEFTPAR lidents_proc RIGHTPAR 
      require
      LEFTBR let_assigns_nondets_updates_locks RIGHTBR
      { let lets, (assigns, nondets, upds,locks) = $8 in
	{   ptr_lets = lets;
	    ptr_name = $2;
            ptr_args = fst $4;
	    ptr_process = snd $4;
	    ptr_reqs = $6;
	    ptr_assigns = assigns; 
	    ptr_nondets = nondets; 
	    ptr_upds = upds;
	    ptr_locks = locks;
            ptr_loc = loc ();
          }
      }
;

let_assigns_nondets_updates_locks:
  | assigns_nondets_updates_locks { [], $1 }
  | LET lident EQ term IN let_assigns_nondets_updates_locks {
	  let lets, l = $6 in
	  ($2, $4) :: lets, l}
;
  
assigns_nondets_updates_locks:
  |  { [], [], [], [] }
  | assign_nondet_update_lock
      {  
	match $1 with
	  | Assign (x, y) -> [x, y], [], [], []
	  | Nondet x -> [], [x], [], []
	  | Upd x -> [], [], [x], []
	  | PLock vp 
	  | PUnlock vp 
	  | PWait vp 
	  | PNotify vp 
	  | PNotifyAll vp -> [], [], [], [vp]
	    
      }
  | assign_nondet_update_lock PV assigns_nondets_updates_locks 
      { 
	let assigns, nondets, upds, locks = $3 in
	match $1 with
	  | Assign (x, y) -> (x, y) :: assigns, nondets, upds, locks
	  | Nondet x -> assigns, x :: nondets, upds, locks
	  | Upd x -> assigns, nondets, x :: upds, locks
	  | PLock vp 
	  | PUnlock vp 
	  | PWait vp 
	  | PNotify vp 
	  | PNotifyAll vp -> assigns, nondets, upds, vp::locks
      }
;

assign_nondet_update_lock:
  | assignment { $1 }
  | nondet { $1 }
  | update { $1 }
  | lock_types { $1 }

;

lock_types:
  | lock { $1 }
  | unlock { $1 }
  | wait { $1 }
  | notify { $1 }
  | notifall { $1}
;


wait:
  | WAIT LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PWait(Wait(VarLock($3,$5)))}
;

notify:
  | NOTIFY LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PNotify(Notify(VarLock($3,$5)))}
;
notifall:
  | NOTIFYALL LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PNotifyAll(NotifyAll(VarLock($3,$5)))}
;

lock:
  | ACQUIRE LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PLock(Lock(VarLock($3,$5))) }
  | ACQUIRELOCK LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PLock(Lock(VarLock($3,$5))) }
  | ACQUIRERLOCK LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PLock(Lock(VarLock($3,$5))) }
  | ACQUIRESEM LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PLock(Lock(VarLock($3,$5))) }
  | ACQUIRECOND LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PLock(Lock(VarLock($3,$5))) }
;

unlock:
  | RELEASE LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PUnlock(Unlock(VarLock($3,$5))) }
  | RELEASELOCK LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PUnlock(Unlock(VarLock($3,$5))) }
  | RELEASERLOCK LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PUnlock(Unlock(VarLock($3,$5))) }
  | RELEASESEM LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PUnlock(Unlock(VarLock($3,$5))) }
  | RELEASECOND LEFTPAR var_or_array_term COMMA lident RIGHTPAR { PUnlock(Unlock(VarLock($3,$5))) }
;

assignment:
  | mident AFFECT term
    {
      if Consts.mem $1 then raise Parsing.Parse_error;
      Assign ($1, PUTerm $3)
    }
  | mident AFFECT CASE switchs
    { Assign ($1, PUCase $4) }
;

nondet:
  | mident AFFECT DOT
    {
      if Consts.mem $1 then raise Parsing.Parse_error;
      Nondet $1
    }
  | mident AFFECT QMARK
    {
     if Consts.mem $1 then raise Parsing.Parse_error;
      Nondet $1
    }
;

require:
  | { PAtom (AAtom (Atom.True)) }
  | REQUIRE LEFTBR expr RIGHTBR { $3 }
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
	let sw = [(a, $6); (PAtom (AAtom Atom.True), TTerm (Access($1, js)))] in
	Upd { pup_loc = loc (); pup_arr = $1; pup_arg = js; pup_swts = sw}  }
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
      if Consts.mem $1 then Const (MConst.add (ConstName $1) 1 MConst.empty)
      else Elem ($1, sort $1) }
  | proc_name { Elem ($1, Var) }
;

top_id_term:
  | var_term { match $1 with
                 | Elem (v, Var) -> TVar v
                 | _ -> TTerm $1 }
;


array_term:
  | mident LEFTSQ proc_name_list_plus RIGHTSQ {
    Access ($1, $3)
  }
;

var_or_array_term:
  | var_term { $1 }
  | array_term { $1 }
  | SPROCS { let s = Hstring.make $1 in Elem(s,SystemProcs)}
;

arith_term:
  | var_or_array_term PLUS constnum 
      { Arith($1, MConst.add $3 1 MConst.empty) }
  | var_or_array_term MINUS constnum 
      { Arith($1, MConst.add $3 (-1) MConst.empty) }
  | var_or_array_term PLUS mident 
    {
      if not (Consts.mem $3) then raise Parsing.Parse_error;
      Arith($1, MConst.add (ConstName $3) 1 MConst.empty)
    }
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

proc_manip:
  | ADDPROC LEFTPAR var_or_array_term RIGHTPAR
      { (*let pr = Elem($3, Var) in*) TTerm (ProcManip([$3], PlusOne)) }
  | SUBPROC LEFTPAR var_or_array_term RIGHTPAR
      { (*let pr = Elem($3, Var) in*) TTerm (ProcManip([$3], MinusOne)) }
  | COMPPROC LEFTPAR var_or_array_term COMMA var_or_array_term RIGHTPAR
      { (*let pr = Elem($3, Var) in
	let pr2 = Elem($5, Var) in*)
	TTerm (ProcManip([$3;$5], CompProcs)) }
;

term:
  | SPROCS { let s = Hstring.make $1 in TTerm (Elem(s,SystemProcs))}
  | proc_manip { $1 }
  | top_id_term { $1 } 
  | array_term { TTerm $1 }
  | arith_term { Smt.set_arith true; TTerm $1 }

  ;

lident:
  | LIDENT { Hstring.make $1 }
;

const_proc:
  | CONSTPROC {let h,s = $1 in
	       if (not Options.interpreter) && (int_of_string s > !Options.size_proc)
	       then raise Parsing.Parse_error;
	       Hstring.make (h^s) }
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
 

lidents_proc_plus:
  | lident { [$1], None }
  | lident lidents_proc_plus { $1::(fst $2), (snd $2) }
  | LEFTSQ lident RIGHTSQ { [$2], Some $2 }
  | LEFTSQ lident RIGHTSQ lidents_plus { $2::$4, Some $2 }
; 
lidents_proc:
  | { [], None }
  | lidents_proc_plus {$1 }
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
  | IF expr THEN expr ELSE expr %prec prec_ite { let pt = PIte ($2, $4, $6) in
						 Format.eprintf "ITE: %a@." Ptree.print pt; pt
						  }
  | FORALL lidents_plus_distinct DOT expr %prec prec_forall { PForall ($2, $4) }
  | EXISTS lidents_plus_distinct DOT expr %prec prec_exists { PExists ($2, $4) }
  | FORALL_OTHER lident DOT expr %prec prec_forall { PForall_other ([$2], $4) }
  | EXISTS_OTHER lident DOT expr %prec prec_exists { PExists_other ([$2], $4) }  
;

simple_expr:
  | literal { PAtom $1 }
  | LEFTPAR expr RIGHTPAR { $2 }
  | lident LEFTPAR expr_or_term_comma_list RIGHTPAR { app_fun $1 $3 }
  | term EQ CASE switchs { (*List.iter (fun (x,y) ->
    let t = match y with
      | TVar v -> Elem(v, Var)
      | TTerm tt -> tt
    in 
    Format.eprintf "--- %a : %a@." Ptree.print x Types.Term.print t) $4;*)
    let rec aux l  =
      match l with
	| [] -> PAtom(AAtom(Atom.True))
	| hd::tl ->
	  let form, tt = hd in
	  PIte(form, PAtom(AEq($1,tt)), aux tl)
    in
    let thing = aux $4 in
    Format.eprintf "Final Ite: %a@." Ptree.print thing;
    thing
			   


			 }
;



expr_or_term_comma_list:
  | { [] }
  | term  { [PT $1] }
  | expr  { [PF $1] }
  | term COMMA expr_or_term_comma_list { PT $1 :: $3 }
  | expr COMMA expr_or_term_comma_list { PF $1 :: $3 }
;


top_proc_name:
  | CONSTPROC { let h,s = $1 in
		 Hstring.make (h^s)
	        }
  
;

top_proc_name_list_plus:
  | top_proc_name { [$1] }
  | top_proc_name COMMA top_proc_name_list_plus { $1::$3 }
;

top_level_trans:
  | lident LEFTPAR RIGHTPAR { ($1, [])}
  | lident LEFTPAR top_proc_name_list_plus RIGHTPAR { ($1, $3)}    
;

toplevel_trans_list:
  | top_level_trans { [$1] }
  | top_level_trans PV toplevel_trans_list { $1::$3 }
;


toplevel_assign:
  | mident AFFECT term  {
    match $3 with
      | TTerm t -> TopAssign($1,Elem($1,Glob), t)
      | TVar v -> TopAssign($1, Elem($1,Glob), Elem(v, Var))}
      
  | mident LEFTSQ proc_name_list_plus RIGHTSQ AFFECT term
      {
	match $6 with
	  | TTerm t -> TopAssign($1, Access($1,$3), t)
	  | TVar v ->  TopAssign($1, Access($1,$3), Elem(v, Var))
      }

;
      
toplevel:
  | TRANSITION toplevel_trans_list { TopTransition $2}
  | STATUS { TopShowEnv }
  | CONSTPROC {TopShowEnv}
  | TEST { TopTest (Hstring.make "1")}
  | HELP { TopHelp }
  | CLEAR { TopClear }
  | RESTART {TopRestart}
  | toplevel_assign { $1 }
  | UNSAFE { TopUnsafe }
  | GENPROC { TopGenProc }
  | KILLPROC { TopKillProc(None)}
  /*| KILLPROC top_proc_name { TopKillProc (Some $2)}*/
  | EXEC { TopExec }      
;
