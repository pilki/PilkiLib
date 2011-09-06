DIRS=.

INCLUDES=$(patsubst %,-I %, $(DIRS))

COQLIBS:=-I ~/devel/cases/src -R ~/devel/cases/theories Case_Tactics

COQC=coqc -q $(INCLUDES) $(COQLIBS)
COQDEP=coqdep $(INCLUDES) $(COQLIBS)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source


VPATH=$(DIRS)
GPATH=$(DIRS)

SRC=ClassesAndNotations.v  Coqlibext.v  Do_notation.v Coqlib.v

FILES=$(SRC)

proof: $(FILES:.v=.vo)

.SUFFIXES: .v .vo

.v.vo:
	@echo "COQC $*.v"
	@$(COQC) -dump-glob /dev/null $*.v

depend: $(FILES)
	$(COQDEP) $^ \
        > .depend


clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -rf _build
	rm -f doc/coq2html.ml doc/coq2html
	rm -f extraction/*.ml extraction/*.mli



include .depend

FORCE:
