CC=ocamlopt -annot
OCAMLOPTS=-a
LANGUAGELIB=systemj.cmxa
REPORTLIB=error.cmxa
LOGICLIB=logic.cmxa
LANGUAGEDIR=../language
REPORTDIR=../error
REPORTDIR=../induction
UTILDIR=../util
TYPECONV=`ocamlfind query type_conv`
SEXPLIB=`ocamlfind query sexplib`
PRETTYLIB=`ocamlfind query pretty`
BATDIR=`ocamlfind query batteries`
SRC=promela.ml c.ml smt.ml
all: codegen.cmxa


codegen.cmxa: code.cmx
	$(CC) $(OCAMLOPTS) -I $(REPORTDIR) -I $(LANGUAGEDIR) -I	\
	$(UTILDIR) promela.cmx smt.cmx c.cmx -o $@

code.cmx:
	$(CC) -pp "camlp4o -I $(TYPECONV) -I $(SEXPLIB) -I $(PRETTYLIB)	\
	pa_type_conv.cma pa_sexp_conv.cma pa_macro.cmo -DDEBUG" -I	\
	$(REPORTDIR) -I $(LANGUAGEDIR) -I $(BATDIR) -I $(SEXPLIB) -I	\
	$(LOGICLIB) -I $(UTILDIR) -I $(PRETTYLIB) -c $(SRC)

clean:
	rm -rf *cm* *o *a *mli *.annot
