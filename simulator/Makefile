main: mymodel.ml myscene.ml main.ml 
	ocamlc -I +unix unix.cma simlib.cma $^ -o $@

clean:
		rm -f *.cmx *.cmi *.o *.cmo *.out *.cmx *.cma *.a *.cmxa main
