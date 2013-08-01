CC=ocamlopt
LANGUAGELIB=systemj.cmxa
LANGUAGEDIR=../language
SRC=propositionalLogic.ml
all: propositionalLogic.cmxa


propositionalLogic.cmxa: propositionalLogic.cmx
	ocamlfind $(CC) -o $@ -linkpkg -package batteries \
	-I $(LANGUAGEDIR) $(LANGUAGELIB) propositionalLogic.cmx

propositionalLogic.cmx:
	ocamlfind $(CC) -pp "camlp4o pa_macro.cmo -DDEBUG" \
	-o $@ -linkpkg -package batteries -I $(LANGUAGEDIR) -c $(SRC)

clean:
	rm -rf *cm* *o *a *mli
