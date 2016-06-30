.PHONY=all clean test

OCB=ocamlbuild -use-ocamlfind

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# TEST_FILES=$(addsuffix .ml,$(addprefix test/test_int,8 16 32))
TEST_FILES=$(addprefix test/test_int,8 16 32)
TEST_BINARY:=$(TEST_FILES:=.byte)

test: all
	$(OCB) $(TEST_BINARY)

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -r Makefile.coq
