libs := unix.cma graphics.cma 
folders := scenelib

main: scenelib/vector.ml maps.ml traces.mli traces.ml model.mli model.ml scene.ml utils.ml mymodel.ml simulator.ml scenelib/input.ml scenelib/bgraphics.ml scenelib/petrilib.ml myscene.ml main.ml
	ocamlc -I +unix -I `ocamlfind query graphics` -I $(folders) $(libs) $^ -o $@

clean:
		rm -f *.cmx *.cmi *.o *.cmo *.out
