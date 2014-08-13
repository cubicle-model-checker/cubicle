include ./Makefile.config 

INCLUDES= -I lib-num  -I src/common/ -I src/smt/ -I src/
JS_INCLUDE=-I $(JS_DIR)/

OCAMLC=ocamlc.opt -g -annot $(INCLUDES)  $(JS_INCLUDE) $(CAMLP4)
OCAMLLEX=ocamllex.opt
OCAMLYACC=ocamlyacc
OCAMLDEP=ocamldep.opt $(INCLUDES) $(JS_INCLUDE) $(CAMLP4)
JS_RUNTIME= \
   $(JS_DIR)/runtime.js \
   $(JS_DIR)/weak.js \
   missing.js


JS_FLAGS= -linkall
CAMLP4= -pp "camlp4o $(JS_DIR)/pa_js.cmo"

all: web/cubicle.js

NUM_CMOS=\
	lib-num/int_misc.cmo \
	lib-num/nat.cmo \
        lib-num/big_int.cmo \
	lib-num/arith_flags.cmo \
        lib-num/ratio.cmo \
	lib-num/num.cmo

CUBICLE_CMOS = gc.cmo $(addprefix src/,functory.cmo $(filter-out main.cmo common/bitv.cmo, $(CMO)))

# CUBGENERATED = $(addprefix src/, $(GENERATED))

main_js.com:main_js.ml
	$(OCAMLC) -c $(JS_INCLUDE) $(CAMLP4) main_js.ml

ALL_CMOS= $(NUM_CMOS) $(CUBICLE_CMOS) main_js.cmo

cubicle_js.byte: $(ALL_CMOS)
	$(OCAMLC) $(JS_INCLUDE) js_of_ocaml.cma unix.cma -o cubicle_js.byte $(ALL_CMOS) 

web/cubicle.js: cubicle_js.byte $(JS_RUNTIME)
	$(JS_COMP) -o web/cubicle.js $(JS_FLAGS) $(JS_RUNTIME) cubicle_js.byte

clean:
	rm -f cubicle_js.byte web/cubicle.js *.cm? *.annot *~
	rm -rf src
	for i in lib-num; do rm -f $$i/*.cm? $$i/*.o $$i/*~  $$i/*.annot; done

distclean: clean
	rm Makefile.config


.SUFFIXES: .mli .ml .cmi .cmo .cmx .mll .mly .tex .dvi .ps .html

.mli.cmi:
	@true compile -w a $(BFLAGS) $<
	$(if $(QUIET),@echo 'Compiling $@' &&) $(OCAMLC) -c $(BFLAGS) $<

.ml.cmo:
	$(if $(QUIET),@echo 'Compiling $@' &&) $(OCAMLC) -c $(BFLAGS) $<
	@true compile -w a $(BFLAGS) $<

.ml.o:
	@true compile -w a $(BFLAGS) $<
	$(if $(QUIET),@echo 'Compiling $@' &&) $(OCAMLOPT) -c $(OFLAGS) $<

.ml.cmx:
	$(if $(QUIET),@echo 'Compiling $@' &&) $(OCAMLOPT) -c $(OFLAGS) $<
	@true compile -w a $(BFLAGS) $<

.mll.ml:
	$(if $(QUIET),@echo 'Compiling $<' &&) $(OCAMLLEX) $< > /dev/null

.mly.ml:
	$(if $(QUIET),@echo 'Compiling $<' &&) $(OCAMLYACC) -v $<

.mly.mli:
	$(if $(QUIET),@echo 'Compiling $<' &&) $(OCAMLYACC) -v $<

.depend:
	$(OCAMLDEP) $(CAMLP4) -slash *.ml* lib-stdlib/*.ml* lib-num/*.ml* src/common/*.ml* src/smt/*.ml* src/*.ml* > .depend

include .depend
