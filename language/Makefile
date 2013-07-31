OCMLOPTS=-a
OCMALDEBUG=-g
CC=ocamlopt
SRC=systemj.ml

all: systemj.cmxa

systemj.cmxa: check
	$(CC) -pp "camlp4o pa_macro.cmo -DDEBUG" $(OCMLOPTS) systemj.cmx -o $@

check:
	$(CC) -pp "camlp4o pa_macro.cmo -DDEBUG" -c $(SRC)
	cp systemj.cmi ../parser/systemj.cmi
clean:
	rm -rf *cm* *o *a *mli
