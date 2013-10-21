CC=ocamlopt -annot
PARSERLIB=parser.cmxa
LANGUAGELIB=systemj.cmxa
LOGICLIB=logic.cmxa
ERRORLIB=error.cmxa
CODEGENLIB=codegen.cmxa
UTILLIB=util.cmxa

all: compile


compile:
	$(MAKE) -e -C error/ all
	$(MAKE) -e -C language/ all
	$(MAKE) -e -C parser/ all
	$(MAKE) -e -C induction/ all
	$(MAKE) -e -C util/ all
	$(MAKE) -e -C backend/ all
	ocamlfind $(CC) -pp "camlp4o pa_macro.cmo -UDEBUG -USDEBUG" -o	\
	systemjc -syntax batteries.syntax -linkpkg -package batteries	\
	-package sexplib -package pretty -package parmap \
	-thread -I ./language -I ./error -I ./parser -I	\
	./induction -I ./util -I ./backend $(ERRORLIB) $(LANGUAGELIB)	\
	$(PARSERLIB) $(LOGICLIB) $(UTILLIB) $(CODEGENLIB) systemjc.ml

clean:
	$(MAKE) -e -C language/ clean
	$(MAKE) -e -C error/ clean
	$(MAKE) -e -C parser/ clean
	$(MAKE) -e -C induction/ clean
	$(MAKE) -e -C util/ clean
	$(MAKE) -e -C backend/ clean
	$(MAKE) -e -C testsuite/ clean
	rm -rf *.ll *.lle *.bc *.s *.dot *.grf *.part* gmon.out TAGS *.mli *.cm* *.o systemjc \
	*.xml *.annot *_spi* *_ver* *.pml.trail 
