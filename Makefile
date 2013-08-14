CC=ocamlopt
PARSERLIB=parser.cmxa
LANGUAGELIB=systemj.cmxa
LOGICLIB=logic.cmxa
ERRORLIB=error.cmxa

all: compile


compile:
	$(MAKE) -e -C error/ all
	$(MAKE) -e -C language/ all
	$(MAKE) -e -C parser/ all
	$(MAKE) -e -C induction/ all
	ocamlfind $(CC) -pp "camlp4o pa_macro.cmo -DDEBUG" -o systemjc	\
	-linkpkg -package batteries -I ./language -I ./error -I		\
	./parser -I ./induction $(ERRORLIB) $(LANGUAGELIB) $(PARSERLIB)	\
	$(LOGICLIB) systemjc.ml

clean:
	$(MAKE) -e -C language/ clean
	$(MAKE) -e -C error/ clean
	$(MAKE) -e -C parser/ clean
	$(MAKE) -e -C induction/ clean
	rm -rf *.ll *.lle *.bc *.s *.dot *.grf *.part* gmon.out TAGS *.mli *.cm* *.o systemjc
