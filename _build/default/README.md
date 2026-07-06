# McPTS: Building Correct-By-Construction Proof Checkers For Pure Type Systems

McPTS is a tool to generate verified, runnable typechecker for predicative pure type systems.  
This project can be instantiated by specifying a PTS signature, along with a proof that it is
predicative.  From there, it provides an executable, to which we can feed a program in the
associated PTS to check whether this program has the specified type. McPTS is implemented
and verified in Rocq.More specifically, we proved that the typechecking algorithm extracted
from Rocq is sound and complete: a program passes typechecker if and only if it is a well-typed
program in the associated PTS.  Despite being elementary, this serves as a basis for future extensions.

McPTS is a fork of McTT, a project with similar goals, but specialized to Martin-Löf type theory.

## Dependencies

* [OCaml](https://ocaml.org/) 4.14.2
* [Menhir](http://cambium.inria.fr/~fpottier/menhir/)
* [Coq-Menhirlib](https://gitlab.inria.fr/fpottier/menhir/-/tree/master/coq-menhirlib)
* [Coq](https://coq.inria.fr/) 8.20.0
* [Coq-Equations](https://github.com/mattam82/Coq-Equations) 1.3

We recommend to install dependencies in the following way:

```bash
opam update
opam switch create coq-8.20.0 4.14.2
opam pin add coq 8.20.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y menhir coq-equations coq-menhirlib ppx_inline_test
```

## Development

Use the toplevel `make` to build the whole project (from the `mechanization` directory):
```
make
```
Makefile will try to find out the number of your CPU cores and parallel as much as
possible.