.PHONY=all clean tests

OCB=ocamlbuild -use-ocamlfind

all: build extraction tests queens

build: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

extraction: extraction/STAMP

# XXX: This will force the recompilation of refinement/bits.vo
# as it depends on extraction/axioms.vo
extraction/STAMP: build extraction/axioms.v
	rm -f test_*.ml test_*.mli extraction/specs.vo
	$(MAKE) -f Makefile.coq extraction/specs.vo
	mv test_*.ml* extraction/
	touch extraction/STAMP

queens: example/QUEENS example/queens_driver.ml
	$(OCB) example/queens_driver.native

example/QUEENS: build example/queens.v
	rm -f queens.ml queens.mli example/queens.vo
	$(MAKE) -f Makefile.coq example/queens.vo
	mv queens.ml* example/
	touch example/QUEENS

TEST_FILES=$(addprefix extraction/test_int,8 16 32)
TARGET=native
TEST_BINARIES:=$(TEST_FILES:=.$(TARGET))

test:
	mkdir -p test

tests: test extraction $(addsuffix .ml, $(TEST_FILES)) extraction/forall.ml
	$(OCB) -package unix $(TEST_BINARIES)

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(OCB) -clean
	rm -rf Makefile.coq extraction/test_* extraction/STAMP \
	       example/QUEENS example/queens.ml*
