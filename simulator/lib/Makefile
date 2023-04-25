main: color.ml vector.ml button.ml maps.ml scene.ml traces.mli traces.ml model.mli model.ml utils.ml simulator.ml indicator.ml input.ml bgraphics.ml basiclib.ml composition.ml renderer.ml petrilib.ml  
	ocamlc -I `ocamlfind query graphics` graphics.cma $^ -a -o simlib.cma

clean:
		rm -f *.cmx *.cmi *.o *.cmo *.out *.cmx *.cma *.a *.cmxa main
