libs := unix.cma

main: model.ml scene.ml utils.ml stmp.ml simulator.ml main.ml
	ocamlc -I +unix $(libs) $^ -o $@

clean:
		rm -f *.cmx *.cmi *.o *.cmo *.out
