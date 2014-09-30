# CC=ocamlopt -annot -warn-error +a+8 -g
CC=ocamlopt -annot -g
OCAMLOPTS=-a
LANGUAGELIB=systemj.cmxa
REPORTLIB=error.cmxa
LOGICLIB=logic.cmxa
LANGUAGEDIR=../language
REPORTDIR=../error
REPORTDIR=../induction
TYPECONV=`ocamlfind query type_conv`
SEXPLIB=`ocamlfind query sexplib`
PRETTYLIB=`ocamlfind query pretty`
BATDIR=`ocamlfind query batteries`
SRC=util.ml dot.ml
all: util.cmxa


util.cmxa: util.cmx
	$(CC) $(OCAMLOPTS) -I $(REPORTDIR) -I $(LANGUAGEDIR) util.cmx dot.cmx -o $@

util.cmx:
	$(CC) -pp "camlp4o -I $(TYPECONV) -I $(SEXPLIB) -I $(PRETTYLIB)	\
	pa_type_conv.cma pa_sexp_conv.cma pa_macro.cmo -UDEBUG" -I	\
	$(REPORTDIR) -I $(LANGUAGEDIR) -I $(BATDIR) -I $(SEXPLIB) -I	\
	$(LOGICLIB) -I $(PRETTYLIB) -c $(SRC)

clean:
	rm -rf *cm* *o *a *mli *.annot
