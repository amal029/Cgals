CCC ?= ocamlopt -annot -g
OCAMLOPTS=-a
LANGUAGELIB=systemj.cmxa
REPORTLIB=error.cmxa
LANGUAGEDIR=../language
REPORTDIR=../error
TYPECONV=`ocamlfind query type_conv`
SEXPLIB=`ocamlfind query sexplib`
BATDIR=`ocamlfind query batteries`
SRC=propositionalLogic.ml tableauBuchiAutomataGeneration.ml modelSystem.ml
all: logic.cmxa


logic.cmxa: logic.cmx
	$(CCC) $(OCAMLOPTS) -I $(REPORTDIR) -I $(LANGUAGEDIR) propositionalLogic.cmx \
	tableauBuchiAutomataGeneration.cmx modelSystem.cmx -o $@

logic.cmx:
	@echo $(BATDIR)
	@echo $(SEXPLIB)
	ocamlfind $(CCC) -pp "camlp4o -I $(TYPECONV) -I $(SEXPLIB)	\
	pa_type_conv.cma pa_sexp_conv.cma pa_macro.cmo -UDEBUG -USDEBUG	\
	-UPDEBUG -UZDEBUG" -I $(REPORTDIR) -I $(LANGUAGEDIR) -I	\
	$(BATDIR) -I $(SEXPLIB) -c $(SRC)

clean:
	rm -rf *cm* *o *a *mli *.annot
