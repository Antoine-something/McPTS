# McPTS: Building Correct-By-Construction Proof Checkers For Pure Type Systems

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
* [Menhir](http://cambium.inria.fr/~fpottier/menhir/) 20260209
* [Coq-Menhirlib](https://gitlab.inria.fr/fpottier/menhir/-/tree/master/coq-menhirlib) 20260209
* [Rocq](https://rocq-prover.org/) 9.1.1
* [Rocq-Equations](https://github.com/rocq-prover/equations) 1.3.1+9.1

We recommend to install dependencies in the following way:

```bash
# setup OPAM switch
opam update
opam switch create rocq-9.1.1 4.14.2
opam switch rocq-9.1.1
eval $(opam env)

# install Rocq
opam pin -y add rocq 9.1.1
opam repo add rocq-released https://rocq-prover.org/opam/released

# install dependencies
opam install -y dune
dune build mcpts.opam
opam install -y --deps-only .
```

## Build from source

Use the toplevel `make` to build the whole project, including the three examples of verified compilers (from the root directory):

```bash
make
```

Makefile will try to find out the number of your CPU cores and parallel as much as
possible.

In some rare cases, Rocq may complain about incorrect timestamps.  To resolve this issue, run the following command:

```bash
find . -type f -exec touch {} +
```

Once `make` finishes, you can run any of the extracted compiler.
The names of the executable are `mcpts_miniml`, `mcpts_lf`, and `mcpts_mlttcumul`.
For example:

```bash
dune exec mcpts_mlttcumul theories/CaseStudies/MLTTCumul/examples/let-nary.mltt
```