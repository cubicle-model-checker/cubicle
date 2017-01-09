#directory "common";;
#directory "util";;
#directory "smt";;
#load "unix.cma";;
#load "nums.cma";;
#load "version.cmo";;
#load "options.cmo";;
#load "hashcons.cmo";;
#load "hstring.cmo";;
#load "vec.cmo";;
#load "iheap.cmo";;
#load "ty.cmo";;
#load "symbols.cmo";;
#load "term.cmo";;
#load "literal.cmo";;
#load "solver_types.cmo";;
#load "explanation.cmo";;
#load "exception.cmo";;
#load "sum.cmo";;
#load "polynome.cmo";;
#load "intervals.cmo";;
#load "fm.cmo";;
#load "arith.cmo";;
#load "combine.cmo";;
#load "use.cmo";;
#load "timer.cmo";;
#load "uf.cmo";;
#load "cc.cmo";;
#load "solver.cmo";;
#load "z3wrapper.cmo";;
#load "alt_ergo.cmo";;
#load "smt.cmo";;
#load "variable.cmo";;
#load "util.cmo";;
#load "cubtypes.cmo";;
#load "cube.cmo";;
#load "node.cmo";;
#load "dot.cmo";;
#load "cubetrie.cmo";;
#load "prover.cmo";;
#load "instantiation.cmo";;
#load "fixpoint.cmo";;
#load "interval.cmo";;

open Cubtypes;;

let ha = Elem (Hstring.make "A", Var);;
let hb = Elem (Hstring.make "B", Var);;
let hc = Elem (Hstring.make "C", Var);;
let ar = Arith (hb, MConst.singleton (ConstInt (Num.num_of_int 1)) 1);;

let a1 = Atom.Comp (ha, Le, ar);;

let a3 = Atom.Comp (ha, Le, hc);;

let a2 = Atom.Comp (hc, Le, hb);;

let rec print_atoms fmt = function
  | [] -> ()
  | [a] -> Format.fprintf fmt "@[%a@]@," Atom.print a
  | a::l -> Format.fprintf fmt "@[%a@]@," Atom.print a;
    print_atoms fmt l

let la = [a1; a2; a3];;

let () = Format.eprintf "Atoms : @[<v>%a@]@." print_atoms la;;

let im = Interval.map (SAtom.of_list la);;

let () = Format.eprintf "Bound : @[<v>%a@]@." Interval.print im;;

