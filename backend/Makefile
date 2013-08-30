CC=ocamlopt -annot
OCAMLOPTS=-a
LANGUAGELIB=systemj.cmxa
REPORTLIB=error.cmxa
LOGICLIB=logic.cmxa
LANGUAGEDIR=../language
REPORTDIR=../error
REPORTDIR=../induction
TYPECONV=`ocamlfind query type_conv`
SEXPLIB=`ocamlfind query sexplib`
BATDIR=`ocamlfind query batteries`
SRC=uppaal.ml
all: codegen.cmxa


codegen.cmxa: uppaal.cmx
	$(CC) $(OCAMLOPTS) -I $(REPORTDIR) -I $(LANGUAGEDIR) uppaal.cmx -o $@

uppaal.cmx:
	$(CC) -pp "camlp4o -I $(TYPECONV) -I $(SEXPLIB)			\
	pa_type_conv.cma pa_sexp_conv.cma pa_macro.cmo	\
	-UDEBUG" -I $(REPORTDIR) -I $(LANGUAGEDIR) -I	\
	$(BATDIR) -I $(SEXPLIB) -I $(LOGICLIB) -c $(SRC)

clean:
	rm -rf *cm* *o *a *mli
