CC=ocamlopt
LANGUAGELIB=systemj.cmxa
LANGUAGEDIR=../language
SRC=induction.ml
all: induction.cmxa


induction.cmxa: induction.cmx
	ocamlfind $(CC) -o $@ -linkpkg -package batteries \
	-I $(LANGUAGEDIR) $(LANGUAGELIB) induction.cmx

induction.cmx:
	ocamlfind $(CC) -pp "camlp4o pa_macro.cmo -DDEBUG" \
	-o $@ -linkpkg -package batteries -I $(LANGUAGEDIR) -c $(SRC)

clean:
	rm -rf *cm* *o *a *mli
