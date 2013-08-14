CC=ocamlopt
OCAMLOPTS=-a
LANGUAGELIB=systemj.cmxa
REPORTLIB=error.cmxa
LANGUAGEDIR=../language
REPORTDIR=../error
BATDIR=`ocamlfind query batteries`
SRC=propositionalLogic.ml tableauBuchiAutomataGeneration.ml
all: logic.cmxa


logic.cmxa: logic.cmx
	$(CC) $(OCAMLOPTS) -I $(REPORTDIR) -I $(LANGUAGEDIR) propositionalLogic.cmx \
	tableauBuchiAutomataGeneration.cmx -o $@

logic.cmx:
	@echo $(BATDIR)
	$(CC) -pp "camlp4o pa_macro.cmo -DDEBUG" -I $(REPORTDIR) -I $(LANGUAGEDIR) -I	\
	$(BATDIR) -c $(SRC)

clean:
	rm -rf *cm* *o *a *mli
