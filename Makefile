.PHONY=all clean tests

OCB=ocamlbuild -use-ocamlfind

all: test Makefile.coq
	$(MAKE) -f Makefile.coq
	$(shell for i in test_*; do mv $$i test/; done)

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# TEST_FILES=$(addsuffix .ml,$(addprefix test/test_int,8 16 32))
TEST_FILES=$(addprefix test/test_int,8 16 32)
TEST_BYTE:=$(TEST_FILES:=.byte)
TEST_NATIVE:=$(TEST_FILES:=.native)

test:
	mkdir -p test

tests: test all
	$(OCB) $(TEST_NATIVE)

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(OCB) -clean
	rm -rf Makefile.coq test/test_*
