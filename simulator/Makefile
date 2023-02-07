libs := unix.cma graphics.cma

main: model.ml scene.ml utils.ml mymodel.ml simulator.ml scenelib.ml myscene.ml main.ml
	ocamlc -I `ocamlfind query graphics` $(libs) $^ -o $@

clean:
		rm -f *.cmx *.cmi *.o *.cmo *.out
