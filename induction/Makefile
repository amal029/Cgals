CC=ocamlopt
OCAMLOPTS=-a
LANGUAGELIB=systemj.cmxa
LANGUAGEDIR=../language
BATDIR=`ocamlfind query batteries`
SRC=propositionalLogic.ml
all: propositionalLogic.cmxa


propositionalLogic.cmxa: propositionalLogic.cmx
	$(CC) $(OCAMLOPTS) -I $(LANGUAGEDIR) propositionalLogic.cmx -o $@

propositionalLogic.cmx:
	@echo $(BATDIR)
	$(CC) -pp "camlp4o pa_macro.cmo -DDEBUG" -I $(LANGUAGEDIR) -I	\
	$(BATDIR) -c $(SRC)

clean:
	rm -rf *cm* *o *a *mli
