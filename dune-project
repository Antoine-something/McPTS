(lang dune 3.23)
(using menhir 2.1)
(name mcpts)

(generate_opam_files)

(license MIT)
(authors "Antoine Gaulin"
         "Rafael Girardello"
         "Junyoung Jang")
(maintainers "the CompLogic group, McGill University")
(maintenance_intent "(latest)")
(homepage "https://github.com/Antoine-something/McPTS")
(documentation "https://github.com/Antoine-something/McPTS")
(source (github Antoine-something/McPTS))

(package
 (name mcpts)
 (synopsis "A Framework for Mechanizing Pure Type Systems")
 (description "McPTS is a framework for generic mechanizations of extensions of pure type systems (PTS), developped in Rocq.
It implements a modern take on the PTS framework, dubbed PTS*, and provides a verified, runnable typechecker for a variety of predicative languages.
In particular several variants of Martin-Löf type theory are covered.  McPTS also provides the tools to extract implementations in OCaml.
The extracted code is guaranteed equivalent to the theoretical definition of the language, provided that the underlying
PTS* signature satisfies three conditions: Predicativity, functionality, and decidability.")
 (depends
  (ocaml (>= "5.4.0"))
  (coq (= "8.20.1"))
  (menhir (= "20260209"))
  (coq-menhirlib (= "20260209"))
  (coq-equations (= "1.3.1+8.20"))
  (ppx_expect (>= "0.16.0"))
  (sherlodoc :with-doc)))

