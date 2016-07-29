include ./Makefile.config 

LWT_DIR=$(shell ocamlfind query lwt)
INCLUDES= -I $(LWT_DIR) -I $(OCAMLGRAPHLIB)/ -I $(JS_DIR)/ 

OCAMLC= ocamlc.opt -g -annot $(INCLUDES) $(CAMLP4)
OCAMLLEX=ocamllex.opt
OCAMLYACC=ocamlyacc
OCAMLDEP=ocamldep.opt $(INCLUDES) $(CAMLP4)
JS_RUNTIME= \
   $(JS_DIR)/runtime.js \
   $(JS_DIR)/weak.js 

BFLAGS = -dtypes -g $(INCLUDES) -annot
OFLAGS = -dtypes -g $(INCLUDES) -annot

JS_FLAGS= -linkall
CAMLP4= -pp "camlp4o $(JS_DIR)/pa_js.cmo"

all: trace.js

TRACE_CMOS = ed_hyper.cmo ed_graph.cmo ed_draw.cmo ed_display.cmo main.cmo 


trace.byte:$(TRACE_CMOS)	
	$(OCAMLC) lwt.cma js_of_ocaml.cma graph.cma \
	-o trace.byte $(TRACE_CMOS)

trace.js: trace.byte $(JS_RUNTIME)
	$(JS_COMP) -o trace.js $(JS_FLAGS) $(JS_RUNTIME) trace.byte

clean:
	rm -f trace.byte trace.js *.cm? *.annot *~	

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
	$(OCAMLDEP) $(CAMLP4) -slash *.ml* > .depend

include .depend
