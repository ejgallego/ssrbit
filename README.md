# A library for Bit Sequences and Bit Sets

This library implements modular arithmetic and logical operations over
bit sequences. It adopts a data-refinement approach, through which one
can switch between proof-oriented and computation-oriented
implementations. In particular, it establishes a refinement between
SSR finset library and bitsets. Finally, it provides a trustworthy
extraction to OCaml, using exhaustive testing for 8 and 16bits
integers.

See the main file for documentation.

## Installation

ssrbit has been implemented in Coq.8.5.2/SSR.1.6 and depends on two
libraries in development version:

+ Damien Rouhling's version of the `paramcoq` plugin: <https://github.com/drouhling/paramcoq>
+ the `paracoq-dev` branch of the `CoqEAL` library: <https://github.com/CoqEAL/CoqEAL/tree/paramcoq-dev/>

Both librairies are included as git submodules in the `lib` directory.

To retrieve the submodules:

    $ cd $SSRBIT_DIR
    $ git submodule init
    $ git submodule update

To build a self-contained installation of ssrbit, we recommend
installing an ad-hoc opam directory:

    $ cd $SSRBIT_DIR
    $ mkdir opam
    $ opam init --root=opam
    $ eval `opam config env --root=$SSRBIT_DIR/opam`
    $ opam repo add coq-released https://coq.inria.fr/opam/released 
    $ opam install -j4 coq.8.5.2 coq-mathcomp-algebra.1.6

To install paramcoq:
 
    $ cd $SSRBIT_DIR/lib/paramcoq
    $ make && make install

To install CoqEAL:

    $ cd $SSRBIT_DIR/lib/CoqEAL/theory
    $ make && make install 
    $ cd $SSRBIT_DIR/lib/CoqEAL/refinements
    $ make && make install 

To build ssrbit:

    $ cd $SSRBIT_DIR
    $ make


## References

This library supersedes the implementation described in

> "From Sets to Bits in Coq",
> Arthur Blot, Pierre-Evariste Dagand, Julia Lawall

With code available at:

- <https://github.com/artart78/coq-bitset>
- <https://github.com/artart78/coq-bits>

In particular, the formalisation of bit vectors (ie. tuples of
booleans) is obtained by canonical lifting of the corresponding
(untyped) implementation on bit sequences (ie. lists of booleans)
rather than directly working on tuples, as was the case in `coq-bits`.

Other interesting references are:

+ Arthur Azevedo de Amorin CoqUtils:
  <https://github.com/arthuraa/coq-utils/blob/master/theories/word.v>
+ Why3 BitVectors: <http://why3.lri.fr/stdlib-0.87.0/bv.html>
+ Coq BitVectors: <https://coq.inria.fr/library/Coq.Bool.Bvector.html>
+ CompCert integers: <https://github.com/AbsInt/CompCert/blob/master/lib/Integers.v>

## Acknowledgments

ssrbit has been developed at the [Centre de Recherche en
Informatique](https://www.cri.ensmp.fr/") of [MINES
ParisTech](http://www.mines-paristech.fr/) (former École de Mines de
Paris) and in LIP6/CNRS/Inria Paris. It is partially supported by the
[FEEVER](http://www.feever.fr) project and the [Emergence(s)
2015](http://www.paris.fr/professionnels/financer-son-projet/appels-a-projets-3563#programme-emergence-s_3)
program.
