libs := graphics.cma unix.cma

main: sutils.ml stmp.ml sgraphics.ml smain.ml
	ocamlc -I `ocamlfind query graphics` $(libs) $^ -o $@

clean:
		rm -f *.cmx *.cmi *.o *.cmo *.out
