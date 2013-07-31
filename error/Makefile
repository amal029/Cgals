LANGDIR=../language
LANGLIB=systemj.cmxa
CC=ocamlopt
SRC=reporting.ml

all: error
	$(CC) -a *.cmx -o error.cmxa

error:
	$(CC) -I $(LANGDIR) $(LANGLIB) -c $(SRC)
	cp reporting.cmi ../parser/error.cmi

clean:
	rm -rf *.cm* *.a *.o
