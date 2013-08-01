PARSERLIB=parser.cmxa
LANGUAGELIB=systemj.cmxa

all: compile


compile:
	$(MAKE) -e -C language/ all
	$(MAKE) -e -C error/ all
	$(MAKE) -e -C parser/ all
	$(MAKE) -e -C induction/ all
	ocamlfind ocamlopt -o systemjc -linkpkg -package batteries \
	-I ./language -I ./error -I ./parser \
	$(LANGUAGELIB) $(PARSERLIB) systemjc.ml 
	ctags -R -e *

clean:
	$(MAKE) -e -C language/ clean
	$(MAKE) -e -C error/ clean
	$(MAKE) -e -C parser/ clean
	$(MAKE) -e -C induction/ clean
	rm -rf *.ll *.lle *.bc *.s *.dot *.grf *.part* gmon.out TAGS *.mli *.cm* *.o systemjc
