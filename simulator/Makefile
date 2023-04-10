libs := unix.cma graphics.cma 
folders := scenelib

main: maps.ml traces.mli traces.ml model.mli model.ml scene.ml utils.ml mymodel.ml simulator.ml scenelib/petrilib.ml myscene.ml main.ml
	ocamlc -I +unix -I `ocamlfind query graphics` -I $(folders) $(libs) $^ -o $@

clean:
		rm -f *.cmx *.cmi *.o *.cmo *.out
