##########################################################################
#                                                                        #
#                              Cubicle                                   #
#                                                                        #
#                       Copyright (C) 2011-2014                          #
#                                                                        #
#                  Sylvain Conchon and Alain Mebsout                     #
#                       Universite Paris-Sud 11                          #
#                                                                        #
#                                                                        #
#  This file is distributed under the terms of the Apache Software       #
#  License version 2.0                                                   #
#                                                                        #
##########################################################################

QUIET=""

# where to install the binaries
DESTDIR=
prefix=/usr/local
exec_prefix=${prefix}
BINDIR=$(DESTDIR)${exec_prefix}/bin
LIBDIR=$(DESTDIR)${exec_prefix}/lib/cubicle
DATADIR=$(DESTDIR)${datarootdir}
DATAROOTDIR=$(DESTDIR)${prefix}/share

# where to install the man page
MANDIR=$(DESTDIR)${datarootdir}/man

# other variables set by ./configure
OCAMLC   = ocamlc.opt
OCAMLOPT = ocamlopt.opt
OCAMLDEP = ocamldep
OCAMLLEX = ocamllex
OCAMLYACC= ocamlyacc
MENHIR   = menhir
OCAMLLIB = /home/mattias/.opam/4.02.0/lib/ocaml
FUNCTORYLIB = -I /home/mattias/.opam/4.02.0/lib/functory
Z3LIB = 
Z3CCFLAGS = 
OCAMLBEST= opt
OCAMLVERSION = 4.02.0
OCAMLWIN32 = no
EXE = 

INCLPATHS = $(FUNCTORYLIB) $(Z3LIBS) -I common/ -I smt/
INCLUDES = $(INCLPATHS) $(Z3CCFLAGS)

BFLAGS = -dtypes -g $(INCLUDES) -annot
OFLAGS = -dtypes -g $(INCLUDES) -annot

REQBIB= nums.cma unix.cma functory.cma

ifeq ($(Z3LIB),)
  BIBBYTE=$(REQBIB)
else
  BIBBYTE=$(REQBIB) z3ml.cma
endif

BIBBYTE=$(REQBIB)

BIBOPT=$(BIBBYTE:.cma=.cmxa)

# main target
#############

NAME = cubicle
BYTE=$(NAME).byte
OPT=$(NAME).opt

all: make_functory $(OCAMLBEST) 

# configuration of the fake functory library
############################################


make_functory:
	@if [ -z "$(FUNCTORYLIB)" ]; then \
	cp -f fake_functory.mli functory.mli;\
	cp -f fake_functory.ml functory.ml;\
	$(OCAMLC) -c functory.mli;\
	$(OCAMLC) -o functory.cma -a functory.ml;\
	$(OCAMLOPT) -c functory.ml;\
	$(OCAMLOPT) -o functory.cmxa -a functory.cmx;\
	fi

# configuration of the Z3 wrapper
#################################


smt/z3wrapper.ml: smt/z3wrapper_actual.ml smt/z3wrapper_fake.ml config.status
	@rm -f smt/z3wrapper.ml
	@echo "(*------------ Generated file, do not modify ------------*)\n" > smt/z3wrapper.ml
	@if [ -z "$(Z3LIB)" ]; then \
	cat smt/z3wrapper_fake.ml >> smt/z3wrapper.ml;\
	else \
	cat smt/z3wrapper_actual.ml >> smt/z3wrapper.ml;\
	fi;\
	chmod -w smt/z3wrapper.ml


# bytecode and native-code compilation
######################################

SMTCMO = smt/exception.cmo smt/symbols.cmo \
	 smt/ty.cmo smt/term.cmo smt/literal.cmo \
         smt/solver_types.cmo smt/explanation.cmo \
         smt/polynome.cmo smt/uf.cmo smt/use.cmo \
	 smt/intervals.cmo smt/fm.cmo smt/arith.cmo smt/sum.cmo \
         smt/combine.cmo smt/cc.cmo smt/solver.cmo \
	 smt/enumsolver_types.cmo smt/enumsolver.cmo smt/alt_ergo.cmo \
	 smt/z3wrapper.cmo smt/smt.cmo

COMMONCMO = common/timer.cmo common/hashcons.cmo common/hstring.cmo\
	    common/vec.cmo common/heap.cmo common/iheap.cmo\
	    common/bitv.cmo

CMO = version.cmo options.cmo \
      $(COMMONCMO) $(SMTCMO) \
      util.cmo variable.cmo types.cmo \
      cube.cmo node.cmo regexp.cmo ptree.cmo parser.cmo lexer.cmo  pretty.cmo \
      instantiation.cmo dot.cmo cubetrie.cmo prover.cmo safety.cmo fixpoint.cmo\
      pre.cmo forward.cmo state.cmo kmeans.cmo enumerative.cmo approx.cmo \
      far_util.cmo far_cube.cmo far_modules.cmo far_graph.cmo \
      far_refine.cmo far_bads.cmo far_close.cmo stats.cmo far_unwind.cmo \
      far.cmo bwd.cmo brab.cmo typing.cmo trace.cmo main.cmo

CMX = $(CMO:.cmo=.cmx)

MAINCMO = $(CMO) main.cmo
MAINCMX = $(MAINCMO:.cmo=.cmx)
KMEANSCMO = kmeans.cmo
KMEANSCMX = $(KMEANSCMO:.cmo=.cmx)

GENERATED = version.ml parser.ml parser.mli lexer.ml smt/z3wrapper.ml

byte: $(NAME).byte
opt: $(NAME).opt

kmeans: $(KMEANSCMX)
	$(OCAMLOPT) $(OFLAGS) -o $@ $(BIBOPT) $^

$(NAME).byte: $(MAINCMO)
	$(if $(QUIET),@echo 'Linking $@' &&) \
	$(OCAMLC) $(BFLAGS) -o $@ $(BIBBYTE) $^

$(NAME).opt: $(MAINCMX)
	$(if $(QUIET),@echo 'Linking $@' &&) \
	$(OCAMLOPT) $(OFLAGS) -o $@ $(BIBOPT) $^

VERSION=1.1.1a
# comment the following line for release
SVNREV=-$(shell svnversion -n)

VERSION_STR=$(VERSION)$(SVNREV)

version.ml: config.status
	@echo "let version = \""$(VERSION_STR)"\"" > version.ml
	@echo "let date = \""`date`"\"" >> version.ml
	@echo "let libdir = \""$(LIBDIR)"\"" >> version.ml

# generic rules
###############

.SUFFIXES: .mli .ml .cmi .cmo .cmx .mll .mly

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


# file headers
##############
headers:
	headache -c doc/headache_config.txt -h doc/cubicle_header.txt \
		Makefile.in configure.in *.ml *.ml[ily] \
		common/*.ml common/*.mli smt/*.ml smt/*.mli

# Emacs tags
############

tags:
	find . -name "*.ml*" | sort -r | xargs \
	etags "--regex=/let[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/let[ \t]+rec[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/and[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/type[ \t]+\([^ \t]+\)/\1/" \
              "--regex=/exception[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/val[ \t]+\([^ \t]+\)/\1/" \
	      "--regex=/module[ \t]+\([^ \t]+\)/\1/"

# installation
##############

install:
	mkdir -p $(BINDIR)
	cp -f $(NAME).$(OCAMLBEST) $(BINDIR)/$(NAME)$(EXE)
	@echo "Installation completed in $(BINDIR). You may want to copy (doc/)emacs/cubicle-mode.el in your emacs.d if you use Emacs."

install-byte:
	mkdir -p $(BINDIR)
	cp -f $(NAME).byte $(BINDIR)/$(NAME)$(EXE)

install-opt:
	mkdir -p $(BINDIR)
	cp -f $(NAME).opt $(BINDIR)/$(NAME)$(EXE)

install-man:
	mkdir -p $(MANDIR)/man1
	cp -f doc/*.1 $(MANDIR)/man1




# clean
#######

clean:: 
	@rm -f *.cm[iox] *.o *~ *.annot
	@rm -f common/*.cm[iox] common/*.o common/*~ common/*.annot
	@rm -f smt/*.cm[iox] smt/*.o smt/*~ smt/*.annot
	@rm -f $(GENERATED) *.output
	@rm -f $(NAME).byte $(NAME).opt
	@rm -f functory.*

# depend
########

.depend depend:: $(GENERATED)
	@rm -f .depend
	@$(OCAMLDEP) -slash -I common/ -I smt/ \
	common/*.ml common/*.mli smt/*.ml smt/*.mli \
	*.ml *.mli > .depend


include .depend

# Makefile is rebuilt whenever Makefile.in or configure.in is modified
######################################################################

Makefile: Makefile.in config.status
	./config.status

config.status: configure
	./config.status --recheck

configure: configure.in
	autoconf 


# export
########

DATE=$(shell date +%d/%m/%Y)
LONGDATE=$(shell date +%Y%m%d%H%M)

EXPORTDIR=$(NAME)-$(VERSION)
TAR=$(EXPORTDIR).tar

EXPORTAE=alt-ergo-light
TARAE=$(EXPORTAE).tar

WEB = $$HOME/WWW/cubicle/

SMTFILES = smt/arith.ml smt/arith.mli smt/cc.ml smt/cc.mli smt/combine.ml\
	   smt/combine.mli smt/exception.ml smt/exception.mli\
	   smt/explanation.ml smt/explanation.mli smt/fm.ml smt/fm.mli\
	   smt/intervals.ml smt/intervals.mli smt/literal.ml\
	   smt/literal.mli smt/polynome.ml smt/polynome.mli smt/sig.mli\
	   smt/smt.ml smt/smt.mli smt/smt_sig.mli smt/alt_ergo.ml smt/alt_ergo.mli\
	   smt/z3wrapper_fake.ml smt/z3wrapper_actual.ml smt/z3wrapper.mli\
	   smt/solver.ml smt/solver.mli\
	   smt/solver_types.ml smt/solver_types.mli smt/enumsolver.ml\
	   smt/enumsolver.mli smt/enumsolver_types.ml smt/enumsolver_types.mli\
	   smt/sum.ml smt/sum.mli\
	   smt/symbols.ml smt/symbols.mli smt/term.ml smt/term.mli\
	   smt/ty.ml smt/ty.mli smt/uf.ml smt/uf.mli smt/use.ml smt/use.mli

COMMONFILES = common/hashcons.ml common/hashcons.mli common/heap.ml\
	      common/heap.mli common/hstring.ml common/hstring.mli\
	      common/iheap.ml common/iheap.mli common/timer.ml\
	      common/timer.mli common/vec.ml common/vec.mli\
	      common/bitv.ml common/bitv.mli

AELIGHTFILES = alt-ergo-light/Makefile.in alt-ergo-light/.depend\
	       alt-ergo-light/configure.in alt-ergo-light/configure

FILES = approx.ml approx.mli ast.mli ptree.mli ptree.ml\
        brab.ml brab.mli bwd.ml bwd.mli\
	cube.ml cube.mli cubetrie.ml cubetrie.mli dot.ml dot.mli\
	enumerative.ml enumerative.mli fake_functory.ml fake_functory.mli\
	far_util.ml far_cube.ml far_modules.ml far_refine.ml far_graph.ml \
        far_unwind.ml far_bads.ml far_close.ml far.ml \
	fixpoint.ml fixpoint.mli forward.ml forward.mli\
	instantiation.ml instantiation.mli kmeans.mli kmeans.ml lexer.mll main.ml\
	node.ml node.mli options.ml options.mli oracle.mli\
	parser.mly pre.ml pre.mli pretty.ml pretty.mli prover.ml prover.mli\
	regexp.ml \
	safety.ml safety.mli state.ml state.mli stats.ml stats.mli trace.ml trace.mli\
	types.ml types.mli typing.ml typing.mli util.ml util.mli\
	variable.ml variable.mli version.ml

EXAMPLES = bakery.cub dijkstra.cub distrib_channels.cub jml.cub\
	   ricart_abdulla.cub szymanski_at.cub berkeley.cub flash_eager.cub\
	   german_pfs.cub german_undip.cub illinois.cub mesi.cub\
	   moesi.cub synapse.cub swimming_pool.cub xerox_dragon.cub\
	   sense_barrier.cub flash.cub flash_abstr.cub flash_nodata.cub\
	   flash_buggy.cub szymanski_na.cub chandra_toueg.cub\
	   german_baukus.cub german.ctc.cub bakery_lamport.cub\
	   bakery_lamport_bogus.cub bakery_lamport_na.cub\
	   bakery_lamport_na_wb.cub bakery_na.cub

DOCFILES = cubicle.1 intro.txt ocamldoc.css

OTHERFILES = .depend configure.in configure Makefile.in CHANGES README COPYING

ARCH = $(shell uname -m)
OSNAME = $(shell uname -s)

binary: $(OPT)
	strip $(OPT)
	cp $(OPT) export/$(NAME)-$(VERSION)-$(OSNAME)-$(ARCH)

export-alt-ergo-light:
	mkdir -p export/$(EXPORTAE)/
	mkdir -p export/$(EXPORTAE)/smt
	mkdir -p export/$(EXPORTAE)/common
	cp $(SMTFILES) export/$(EXPORTAE)/smt
	cp $(COMMONFILES) export/$(EXPORTAE)/common
	cp $(AELIGHTFILES) export/$(EXPORTAE)/
#	cp smt/smt.mli export/$(EXPORTAE)/altErgoLight.mli
	mkdir -p export/$(EXPORTAE)/doc/
	ocamldoc -html -colorize-code -d export/$(EXPORTAE)/doc/ -I smt -I common smt/smt.mli common/hstring.mli
	cd export ; tar cf $(TARAE) $(EXPORTAE) ; gzip -f --best $(TARAE)


export/$(EXPORTDIR).tar.gz:
	mkdir -p export
	mkdir -p export/$(EXPORTDIR)
	mkdir -p export/$(EXPORTDIR)/smt
	mkdir -p export/$(EXPORTDIR)/common
	mkdir -p export/$(EXPORTDIR)/examples
	mkdir -p export/$(EXPORTDIR)/emacs
	mkdir -p export/$(EXPORTDIR)/doc
	cp $(SMTFILES) export/$(EXPORTDIR)/smt
	cp $(COMMONFILES) export/$(EXPORTDIR)/common
	cp $(FILES) export/$(EXPORTDIR)/
	cp $(OTHERFILES) export/$(EXPORTDIR)/
	cd doc/; cp $(DOCFILES) ../export/$(EXPORTDIR)/doc/; cd ..
	cd examples/; cp $(EXAMPLES) ../export/$(EXPORTDIR)/examples/; cd ..
	cp doc/emacs/cubicle-mode.el export/$(EXPORTDIR)/emacs/
	cd export ; tar cf $(TAR) $(EXPORTDIR) ; gzip -f --best $(TAR)

export: export/$(EXPORTDIR).tar.gz

release: export/$(EXPORTDIR).tar.gz doc
	mkdir -p export/release
	mkdir -p export/release/examples/
	cp export/$(TAR).gz export/release/
	cp export/$(EXPORTDIR)/examples/* export/release/examples/
	cp doc/website/* export/release/
	cd export/release/; \
	  sed -i '' 's/#version#/$(VERSION)/g' index.html; \
	  sed -i '' 's@#date#@$(DATE)@g' index.html; \
	  sed -i '' -e '/#CHANGELOG#/{r ../../CHANGES' -e 'd' -e '}' index.html
	mkdir -p $(WEB)/backup/$(LONGDATE)
	mv $(WEB)/*.* $(WEB)/backup/$(LONGDATE)
	cp $(WEB)/backup/$(LONGDATE)/google*.html $(WEB)
	cp -f -R export/release/* $(WEB)
	rm -rf $(WEB)/ocamldoc
	cp -f -R doc/ocamldoc $(WEB)/


# Try Cubicle
#############
export CMO
try: $(GENERATED)
	mkdir -p try-cubicle/src
	mkdir -p try-cubicle/src/smt
	mkdir -p try-cubicle/src/common
	cp $(SMTFILES) try-cubicle/src/smt
	cp $(COMMONFILES) try-cubicle/src/common
	cp $(filter-out main.ml,$(FILES)) try-cubicle/src/
	cp $(GENERATED) try-cubicle/src/
	cp -f fake_functory.mli try-cubicle/src/functory.mli
	cp -f fake_functory.ml try-cubicle/src/functory.ml
	cd try-cubicle; ./configure
	$(MAKE) -C try-cubicle


# ocamldoc
##########
doc:
	mkdir -p doc/ocamldoc
	cp -f doc/ocamldoc.css doc/ocamldoc/style.css
	ocamldoc -html -keep-code -d doc/ocamldoc \
	-t "Cubicle $(VERSION) documentation and source" \
	-intro doc/intro.txt $(INCLPATHS) \
	$(filter-out %.mll %.mly fake_functory.ml, $(FILES)) \
        $(filter-out smt/z3wrapper_fake.ml smt/z3wrapper_actual.ml, $(SMTFILES)) \
	$(COMMONFILES) 

docpdf: 
	mkdir -p doc/ocamldoc/latex
	ocamldoc -latex -keep-code -d doc/ocamldoc -o doc/ocamldoc/latex/doc.tex \
	-t "Cubicle $(VERSION) documentation and source" \
	-intro doc/intro.txt $(INCLPATHS) \
	$(filter-out %.mll %.mly fake_functory.ml, $(FILES)) \
        $(filter-out smt/z3wrapper_fake.ml smt/z3wrapper_actual.ml, $(SMTFILES)) \
	$(COMMONFILES) 
	cd doc/ocamldoc/latex/; rubber -d doc


archi:
	ocamldoc -dot -dot-reduce -o doc/archi.dot \
	-t "Cubicle $(VERSION) architecture" \
	$(INCLPATHS) \
	$(filter-out *.mll *.mly fake_functory.ml fake_functory.mli, $(FILES)) \
	$(COMMONFILES) smt/smt_sig.mli
	dot -G"rotate=0" -Tpdf doc/archi.dot > doc/archi.pdf
	rm -f doc/archi.dot


.PHONY: doc docpdf archi export release
