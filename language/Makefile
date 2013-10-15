OCMLOPTS=-a 
OCMALDEBUG=-g
CC=ocamlopt -annot -warn-error +a+8
SRC=systemj.ml
TYPECONV=`ocamlfind query type_conv`
SEXPLIB=`ocamlfind query sexplib`
BATDIR=`ocamlfind query batteries`

all: systemj.cmxa

systemj.cmxa: check
	$(CC) $(OCMLOPTS) systemj.cmx -o $@

check:
	@echo $(TYPECONV)
	$(CC) -pp "camlp4o -I $(TYPECONV) -I $(SEXPLIB)			\
	pa_type_conv.cma pa_sexp_conv.cma pa_macro.cmo -UDEBUG" -I	\
	$(BATDIR) -I $(SEXPLIB) -I ../error -c $(SRC)
	cp systemj.cmi ../parser/systemj.cmi
clean:
	rm -rf *cm* *o *a *mli
