libs := unix.cma graphics.cma

main: maps.ml traces.mli traces.ml model.mli model.ml scene.ml utils.ml mymodel.ml simulator.ml scenelib.ml myscene.ml main.ml
	ocamlc -I +unix -I `ocamlfind query graphics` $(libs) $^ -o $@

clean:
		rm -f *.cmx *.cmi *.o *.cmo *.out
