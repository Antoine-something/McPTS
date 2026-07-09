# McPTS: Building Correct-By-Construction Proof Checkers For Pure Type Systems
test
McPTS is a tool to generate verified, runnable typechecker for systems of the PTS* framework, which aims to study extensions of pure type systems in a principled, modular manner.
This project can be instantiated by specifying a PTS* signature, along with a proof that it is
predicative, functional, and decidable.  From there, it provides an executable, to which we can feed a program in the
associated PTS* to check whether this program has the specified type. McPTS is implemented
and verified in Rocq. More specifically, we proved that the typechecking algorithm extracted
from Rocq is sound and complete: a program passes typechecker if and only if it is a well-typed
program in the associated PTS*.

McPTS includes three case studies, for MiniML, a variant of LF, and a version of Martin-Löf type theory with a full cumulative universe hierarchy.
All three verified type checkers are extracted separately in their respective locations in 'theories/CaseStudies'.

McPTS is a fork of McTT, a project with similar goals, but specialized to Martin-Löf type theory.

## Dependencies

* [OCaml](https://ocaml.org/) 4.14.2
* [Menhir](http://cambium.inria.fr/~fpottier/menhir/)
* [Coq-Menhirlib](https://gitlab.inria.fr/fpottier/menhir/-/tree/master/coq-menhirlib)
* [Coq](https://coq.inria.fr/) 8.20.0
* [Coq-Equations](https://github.com/mattam82/Coq-Equations) 1.3

We recommend to install dependencies in the following way:

```bash
# setup OPAM switch
opam update
opam switch create coq-8.20.0 4.14.2
opam switch coq-8.20.0
eval $(opam env)

# install Rocq
opam pin -y add coq 8.20.0
opam repo add coq-released https://coq.inria.fr/opam/released

# install dependencies
opam install -y dune
dune build mcpts.opam
opam install -y --deps-only .
```

## Build from source

Use the toplevel `make` to build the whole project, including the three examples of verified compilers (from the root directory):
```
make
```
Makefile will try to find out the number of your CPU cores and parallel as much as
possible.

One `make` finishes, you can run any of the extracted compiler.
The names of the executable are `mcpts_miniml`, `mcpts_lf`, and `mcpts_mlttcumul`.
For example:
```
dune exec mcpts_mlttcumul theories/CaseStudies/MLTTCumul/examples/let_nary.mcpts
```