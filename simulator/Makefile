libs := graphics.cma unix.cma

main: shelp.ml stmp.ml sgraphics.ml smain.ml
	ocamlc -I `ocamlfind query graphics` $(libs) $^ -o $@

clean:
		rm *.cmx *.cmi *.o *.cmo *.out
