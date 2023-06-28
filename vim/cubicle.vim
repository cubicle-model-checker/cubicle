syn clear

syn keyword cubicleType bool int real proc
syn keyword cubicleQuant forall_other exists_other forall exists 
syn keyword cubicleFunction init transition unsafe predicate requires 
syn keyword cubicleDecl var array const type
syn keyword cubicleConditional if else case

syn match cubicleNumber	"\<[0-9]\+\>"
syn match cubicleFloat  "\<[0-9]\+.[0-9]\+\>"
syn keyword cubicleConstant True False
syn match cubicleOperator "&&" "||" "<=>" "=>" "not" 

syn region cubicleComment start="(\*"  end="\*)"

if !exists("did_cubicle_syntax_inits")
  let did_cubicle_syntax_inits = 1
  hi link cubicleType					Type
	hi link cubicleConstant 		Number 
	hi link cubicleNumber				Number
	hi link cubicleFloat				Number
	hi link cubicleComment			Comment
	hi link cubicleConditional 	Conditional
	hi link cubicleFunction			Statement
	hi link cubicleDecl					Statement
	hi link cubicleOperator			Operator
endif
