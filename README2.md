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


# Artifact evaluation

## List of claims

Below is a list of where all the lemmas and theorems discussed in the paper can be found.
We include a more high-level description of the structure of the codebase in the "Additional artifact description" section, as well as a list of the key definitions and their corresponding locations in the codebase.


### Generic properties for arbitrary signatures

Lemma 3.1 (Presupposition) is separated in several lemmas in the mechanization:
- For context equality: the lemma "presup_ctx_eq" in the Coq file "theories/Core/Syntactic/System/Lemmas.v"
- For well-formed substitutions: the lemma "presup_sub" in the Coq file "theories/Core/Syntactic/System/Lemmas.v"
- For well-formed types: the lemma "presup_typ" in the Coq file "theories/Core/Syntactic/System/Lemmas.v"
- For context subtyping: the lemma "presup_wf_ctx_sub" in the Coq file "theories/Core/Syntactic/System/Lemmas.v"
- For well-formed expressions: the lemma "presup_exp" in the Coq file "theories/Core/Syntactic/System/Lemmas.v"
- For expression equality, substitution equality, subtyping, and type equality: the mutual lemmas "presup_exp_eq", "presup_sub_eq", "presup_subtyp", "presup_typ_eq" (respectively) in the Coq file "theories/Core/Syntactic/Presup.v"

Lemma 3.2 (Functionality of evaluation) is separated in several lemmas:
- For the evaluation procedure: the lemma "functional_eval" in the Coq file "theories/Core/Semantic/Evaluation/Lemmas.v"
- For the readback procedure: the lemma "functional_read" in the Coq file "theories/Core/Semantic/Readback/Lemmas.v"
- For the normalization procedure: the lemma "functional_nbe" in the Coq file "theories/Core/Semantic/NbE.v"


Equivalence of standard judgments and annotated judgments (discussed in section 4.2.2) has two parts:
- Completeness of annotated judgments: the mutually defined lemmas "wf_ctx_implies_wf_ctx_ann", "wf_exp_implies_wf_exp_ann", "wf_typ_implies_wf_typ_ann", and "wf_sub_implies_wf_sub_ann" in the Coq file "theories/Core/Syntactic/SystemAnnotated/Lemmas.v"
- Soundness of annotated judgments: the lemma "wf_judg_ann_implies_wf_judg" in  the Coq file "theories/Core/Syntactic/SystemAnnotated/Lemmas.v"


### Normalization for predicative signatures

#### Completeness of NbE

Functionality of the PERs (mentionned in text, section 4.1) has three parts:
- Functionality of the PER for sorts: the lemmas "per_sort_elem_right_irrel", "per_sort_elem_left_irrel", and "per_sort_elem_cross_irrel" in the Coq file "theories/Core/Semantic/PER/Lemmas.v"
- Functionality of the PER for types: the lemmas "per_typ_elem_right_irrel", "per_typ_elem_left_irrel", and "per_typ_elem_cross_irrel" in the Coq file "theories/Core/Semantic/PER/Lemmas.v"
- Functionality of the PER for contexts: the lemmas "per_ctx_env_right_irrel", "per_ctx_env_left_irrel", and "per_ctx_env_cross_irrel" in the Coq file "theories/Core/Semantic/PER/Lemmas.v"


Theorem 4.1 (Realizability of the PER model): the lemma "realize_per_typ_elem_gen" in the Coq file "theories/Core/Semantic/Realizability.v"


Theorem 4.2 (Fundamental theorem of completeness): the theorem "completeness_fundamental" in the Coq file "theories/Core/Completeness/FundamentalTheorem.v".  Since this is a very large proof, most of the individual cases are proven separately in the corresponding files of the "theories/Core/Completeness" folder (e.g. the cases for functions are in the Coq file "theories/Core/Completeness/FunctionCases.v")


Corollary 4.3 (Completeness of normalization): the theorem "completeness" in the Coq file "theories/Core/Completeness.v"


#### Soundness of NbE


Functionality of the gluing relations (Section 4.2.1) has two parts:
- Functionality of the gluing relations for sorts: the lemma "functional_glu_sort_elem" in the Coq file "theories/Core/Soundness/LogicalRelation/CoreLemmas.v"
- Functionality of the gluing relations for types: the lemma functional_glu_typ_elem" in the Coq file "theories/Core/Soundness/LogicalRelation/CoreLemmas.v"
- Functionality of the gluing relations for contexts: the corollary "functional_glu_ctx_env" in the Coq file "theories/Core/Soundness/LogicalRelation/Lemmas.v"


Theorem 4.4 (Realizability of the gluing model): the theorem "realize_glu_typ_elem_gen" in the Coq file "theories/Core/Soundness/Realizability.v"


Theorem 4.5 (Fundamental theorem of soundness):
- For annotated judgments: the theorem "soundness_fundamental" in the Coq file "theories/Core/Soundness/FundamentalTheorem.v"
- For ordinary judgents: the theorems "soundness_fundamental_ctx", "soundness_fundamental_exp", "soundness_fundamental_typ", and "soundness_fundamental_sub" in the Coq file "theories/Core/Soundness/FundamentalTheorem.v"


Theorem 4.6 (Soundness of normalization): the theorem "soundness" in the Coq file "theories/Core/Soundness.v"


### Algorithmic type checking for predicative and functional signatures


Theorem 5.1 (Equivalence of algorithmic and declarative subtyping):
- Soundness of algorithmic subtyping for normal types: the lemma "alg_subtying_nf_sound" in the Coq file "theories/Algorithmic/Subtyping/Lemmas.v"
- Completeness of algorithmic subtyping: the lemma "alg_subtyping_complete" in the Coq file "theories/Algorithmic/Subtyping/Lemmas.v"
- Soundness of algorithmic subtyping for arbitrary types: the lemma "alg_subtyping_sound" in the Coq file "theories/Algorithmic/Subtyping/Lemmas.v"


Theorem 5.2 (Soundness of algorithmic typing): the lemma "alg_type_sound" in the Coq file "theories/Algorithmic/Typing/Lemmas.v"


Theorem 5.3 (Completeness of algorithmic typing): the lemma "alg_type_complete" in the Coq file "theories/Algorithmic/Typing/Lemmas.v".  Note this lemma has several trivial parts (implications of True), which are needed to use the mutual induction principle of the judgments.



### Extraction of verified type checkers for predicative, functional, and decidable signatures


This section does not have any formal claims, but the ability to extract type checkers is the central claim of the paper, so it deserves a discussion.  The crucial part of the extraction is to provide a functional implementation of our judgments in Coq.  This is done across the several files in "theories/Extraction", e.g. "theories/Extraction/TypeCheck.v" implements the algorithmic type checking judgment.

The extraction itself is enabled in the case studies (folder "theories/CaseStudies"), by extracting the "main" function of the corresponding "Entrypoint.v" file (e.g. "theories/CaseStudies/LF/Entrypoint.v").  Each case study has a generated parser and a "Frontend.v" file that performs elaboration from a surface language to our internal representation.  The "main" function basically invokes the generated parser, performs elaboration, and calls the type checker.


## Download, installation, and sanity-testing

### Information about the virtual machine image

We have tested the virtual machine image on VirtualBox version 7.2.18.

The guest OS is Ubuntu 22.04.5 LTS.

The virtual machine image uses 2 CPU cores, 4GB of RAM, and 16MB of VRAM.

Should you need it, the password is 'artifact'.




### Accessing the artifact

__Note.__ By the time you reach this point, you are already running the virtual image, so this step should be done.

First, install VirtualBox.  We recommend version 7.2.18, since this is the only one we tested.
Second, download the virtual machine image from the Zenodo link and import it to VirtualBox.
Third, run the artifact using VirtualBox.

To access the artifact itself, open the 'McPTS' folder on the desktop.
Alternatively, you can access it from the terminal by running the following command:

```
cd Desktop/McPTS
```

### Dependencies of the artifact

All dependencies are pre-installed in the virtual machine image.
For your reference, we still list them here:

* [OCaml](https://ocaml.org/) 4.14.2
* [Menhir](http://cambium.inria.fr/~fpottier/menhir/) 20240715
* [Coq-Menhirlib](https://gitlab.inria.fr/fpottier/menhir/-/tree/master/coq-menhirlib) 20240715
* [Coq](https://coq.inria.fr/) 8.20.0
* [Coq-Equations](https://github.com/mattam82/Coq-Equations) 1.3

Further information on installing dependencies is provided in the "Additional artifact description" section of this README file.


### Compiling the artifact.

__Warning.__ Compilation can take a long time.
In our slowest tests, it took up to 30 minutes, using 11th generation i7 cores at 2.8GHz.
It also sometimes seem like compilation is stuck (e.g. on "theories/Core/Soundness/NatCases.v"), but it is not.


The artifact is pre-compiled on the virtual machine image to save time for the reviewers.
Given that correctness of Coq projects is validated by type checking, the reviewers may still want to run compilation themselves.
We provide a makefile with three main flags of interest to reviewers:
- `make clean` cleans the repository of all compilation files
- `make` compiles all the proofs, but not the case studies
- `make extract` compiles all the proofs and case studies, and performs the extraction of Coq implementations to OCaml.

Further information on compilation is provided in the "Additional artifact description" section of this README file.


### Sanity checks

`coqchk` goes through a compiled Coq file and tells which axioms are used (admitted results are counted as axioms) and whether any non-standard features are used.
We have included a script that runs `coqchk` on all the Coq files, which you can run as follows:


```
./check.sh
```

The output should state that all modules were
successfully checked, as well as listing the axioms used in McPTS:
- Coq.Logic.ProofIrrelevance.proof_irrelevance
- Coq.Logic.FunctionalExtensionality.functional_extensionality_dep
- Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq (equivalent to UIP)


### Case studies and running tests

We have performed three case studies and extracted their associated compilers.
The names of the executable are `mcpts_miniml`, `mcpts_lf`, and `mcpts_mlttcumul`.
Each case study contains a README file detailing the specification of the PTS* signature and the grammar of its corresponding front-end language:
- [MiniML](theories/CaseStudies/MiniML/README.md)
- [Cumulative MLTT](theories/CaseStudies/MLTTCumul/README.md)
- [LF](theories/CaseStudies/LF/README.md)

The executable for each compiler takes a program in the associated front-end language and outputs pretty-printed syntax trees after parsing, elaboration, and normalization.  
Output has the form:

```
Parsed:                                
  <Syntax tree of parsed input>
Elaborated:
  <Syntax tree of elaborated input>
Normalized Result:
  <Syntax tree of normalized result>

```

We provide a number of example programs (i.e. tests) for each of our extracted compilers.
You can run the compiler on an example program using the following pattern:

```
dune exec <executable> <path-to-case-study>/<program>
```

For example:

```
dune exec mcpts_mlttcumul theories/CaseStudies/MLTTCumul/examples/let-nary.mltt
```

Additionally, we provide for each case study a script to run all the tests associated to that case study.
Each script runs the compiler on each included test file and displays the expected output along with the actual output. 
You can run them as follows:
- MiniML: `./test_miniml.sh` 
- Cumulative MLTT: `./test_mlttcumul.sh`
- LF: `./test_lf.sh`

#### Provided examples

#### MiniML
- simple-fn.miniml
- simple-let.miniml
- simple-nat.miniml
- add.miniml
- add-numbers.miniml
- let-two-vars.miniml
- let-mult.miniml

#### Cumulative MLTT:
- simple-fn.mltt
- simple-let.mltt
- simple-nat.mltt
- simple-rec.mltt
- let-two-vars.mltt
- let-nary.mltt

#### LF:
- hoas.lf
- plus.lf
- lambda.lf



## Evaluation instructions

### Step 1: Compilation (Optional)

__\*Warning\*__ 
As discussed prior, compilation can take a long time, and the codebase is pre-compiled.
Consequently, this step can be omitted or performed at any other time of the evaluation.

To compile the artifact from scratch, run the following commands:

```
make clean
make extract
```


### Step 2: Run `coqchk`

`coqchk` is used to verify that we use no non-standard axioms or features.
You can run the provided script to check every file in the repository by running the following command:

```
./check.sh
```

The output is very long since it lists every file in every module, but it ends with a summary of the findings, which should look like this:

```
CONTEXT SUMMARY
===============

* Theory: Set is predicative
  
* Theory: Rewrite rules are not allowed
  
* Axioms:
    Coq.Logic.ProofIrrelevance.proof_irrelevance
    Coq.Logic.FunctionalExtensionality.functional_extensionality_dep
    Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq
  
* Constants/Inductives relying on type-in-type: <none>
  
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
  
* Inductives whose positivity is assumed: <none>
```


### Step 3: Run test programs

Convenience scripts have been provided to run all available tests on each of the three included case studies.
For each test, the scripts output the program being tested, the expected output for comparison, and the result from the compiler.
You can run them as follows:
- MiniML: `./test_miniml.sh` 
- Cumulative MLTT: `./test_mlttcumul.sh`
- LF: `./test_lf.sh`

Instructions on running tests manually can also be found in the above section "Case studies and running tests"





### Step 4: Confirm the correspondence of claims

The last step is to validate that the claims in the paper match the claims in the implementation.
See the "List of claims" section above for the locations of each result in the codebase.
The Coq notation is very similar to the notation used in the paper, so it should be straightforward to understand the statements of theorem.



## Additional artifact description


### Installing dependencies

* [OCaml](https://ocaml.org/) 4.14.2
* [Menhir](http://cambium.inria.fr/~fpottier/menhir/) 20240715
* [Coq-Menhirlib](https://gitlab.inria.fr/fpottier/menhir/-/tree/master/coq-menhirlib) 20240715
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


### Detailed compilation instructions

Use the top-level `make` from the root directory to build the core McPTS infrastructure. 
This will compile all the proofs without extracting anything.
Makefile will try to find out the number of your CPU cores and parallel as much as possible.

Compilers defined in a directory `theories/CaseStudies/<name>` can be extracted by using `make extract-<name>` from the top-level. 
Alternatively, every compiler defined in `theories/CaseStudies` can be extracted at once by running `make extract`. 

Our three examples can be compiled at once with `make extract`, or individually with

```
make extract-MiniML
make extract-LF
make extract-MLTTCumul
```

The pattern `make extract-<case-study>` will work for any additional case study without requiring changes to the makefile.


### Structure of the code base

#### Main components

All the Coq files are located in the "theories" folder.
We recommend taking a look at the "_CoqProject" file.
It contains the list of all Coq files in the project, in the order in which they should be consulted.
There are four main components in the project:

1. The "PtsSignature" module include definitions of PTS* signatures and their properties.
All of the subsequent definitions and results are parameterized by at least a PTS* signature, and sometimes also by properties of that signature (predicativity, functionality, and decidability), so the module is imported across the whole codebase.

2. The "Core" module is the largest component and contains everything to do with the declarative definition of PTS*.
   It is separated into four sub-components that build upon the previous ones:
   i. "Syntactic" includes the definition of the language and its type system, and proofs of simple properties.
      The entire "Syntactic" sub-component applies to arbitrary PTS* signatures, with the exception of one theorem to establish that syntactic equality of normal forms is decidable, for which we need the PTS* signature to satisfy the decidability condition.
   ii. "Semantic" includes the definition of the domain model and the normalization procedure, as well as a proof that evaluation is deterministic.
       This applies to arbitrary PTS* signatures.
       The "Semantic" sub-component also includes the definition of PER model and its key properties, in particular the realizability theorem.
       Everything related to PER model is done only for predicative PTS* signatures.
   iii. "Completeness" contains the proof of completeness of normalization.
   	This includes the definitions of logical relations and the associated fundamental theorem.
	Since this proof is large, we instead prove each case as a separate lemma, and organize the cases across different files based on the relevant language features.
	For example, cases related to natural numbers are in the Coq file "NatCases.v", while cases related to contexts are in the file "ContextCases.v".
	(Almost) everything in the "Completess" sub-component requires predicative PTS* signatures.
   iv. "Soundness" focuses on the proof of soundness of normalization.
       This includes the definition of the gluing model and the logical relations, as well as the proofs of realizability and the fundamental theorem, among others.
       Like for completeness, we separate the proof of the fundamental theorem across several lemmas, organized in different files.
       (Almost) everything in the "Soundness" sub-component requires predicative PTS* signatures.
	
3. The "Algorithmic" module includes the definitions of all algorithmic judgments, as well as the proofs that they are equivalent to the declarative judgments.
   The algorithmic judgments depend on normalization, and therefore also requires the predicativity of PTS* signatures.
   The functionality requirement is used only to establish that the type inference procedure really is functional, in the sense that it can only infer a unique type.

4. The "Extraction" module includes a functional implementation of the algorithmic judgments in Coq.
   The type checking algorithm (located in "TypeCheck.v") uses all three properties of signature (predicativity, functionality, and decidability).

#### Case studies

In addition to these four main components, there are the case studies, which are located in "theories/CaseStudies/<name of case study>"
In addition, there is a "Frontend" component, whose main purpose is to provide a generic elaboration procedure to convert named variables into de Bruijn indices.

There are three main cases studies: "MiniML", "LF", and "MLTTCumul".
For these, we include the whole structure described above to perform extraction.
We also include three additional signatures "STLC", "MLTTNonCumul", and "MLTTOmega" to demonstrate the flexibility of our framework.
For these, we did not define a parser, elaborator, or entrypoint, as they would be redundant.

More details on the structure of case studies is discussed below.


### List of key definitions


#### PTS* signatures

Definitions relevant to PTS* signature are located in the folder "theories/PtsSignature".
There are four main definitions:
- PTS* signatures themselve (Definition 2.1) are defined in the Coq file "theories/PtsSignature/Signatures.v", as the record "PtsSig".
- Predicativity of signatures (Definition 2.2) is defined in the Coq file "theories/PtsSignature/Predicativity.v", as the record "PredicativeSig"
- Functionality of signatures (Definition 2.3) is defined in the Coq file "theories/PtsSignature/Functionality.v", as the record "FunctionalSig"
- Decidability of signatures (Definition 2.4) is defined in the Coq file "theories/PtsSignature/Decidability.v", as the record "DecidableSig"


#### Declarative definitions

##### Syntactic definitions

The syntax (Section 3) of an arbitrary PTS* is defined in the Coq file "theories/Core/Syntactic/Syntax.v".
It consists of the mutual definitions "exp" and "sub", and the shorthand "ctx".
The files also includes the notation that use throughout the mechanization.


The declarative judgments (Section 3.1) of an abitrary PTS* are defined in the Coq file "theories/Core/Syntactic/System/Definitions.v".
It consists of several mutual definitions:
- "wf_ctx" (for well-formed contexts),
- "wf_ctx_sub" (for context subtyping),
- "wf_exp" (for typing/well-formed expressions),
- "wf_sub" (for well-formed substitutions),
- "wf_ctx_eq" (for equality of contexts),
- "wf_exp_eq" (for equality of expressions),
- "wf_sub_eq" (for equality of substitutions),
- "wf_subtyp" (for subtyping),
- "wf_typ" (for well-formed types), and
- "wf_typ_eq" (for equality of types.


The annotated judgments (discussed in section 4.2.2) of an arbitrary PTS* are defined in the Coq file "theories/Core/Syntactic/SystemAnnotated/Definitions.v".
It consists of several mutual definitions (one for each ordinary well-formedness judgment):
- "wf_ctx_ann" (for well-formed contexts),
- "wf_exp_ann" (for typing/well-formed expressions),
- "wf_sub_ann" (for well-formed substitutions), and
- "wf_typ_ann" (for well-formed types).


Weakening substitutions (Section 4.2.1) of an arbitrary PTS* are defined in the Coq file "theories/Core/Soundness/Weakening/Definitions.v".


##### Semantic definitions


The domain model (Section 3.2.1) of an arbitrary PTS* is defined in the Coq file "theories/Core/Semantic/Domain.v", by mutual definitions "domain", "domain_ne", "domain_nf", and "env".


Evaluation of syntactic expressions into domain objects (Figure 5) is defined in the Coq file "theories/Core/Semantic/Evaluation/Definitions.v".
It consists of four mutual definitions "eval_exp", "eval_app", "eval_natrec", and "eval_sub".


Readback of domain objects into syntactic normal forms (Figure 6) is defined in the Coq file "theories/Core/Semantic/Readback/Definitions.v".
It consists of three mutual definitions "read_nf", "read_ne", and "read_typ".


The normalization procedures (Section 3.2.4) are defined in the Coq file "theories/Core/Semantic/NbE.v".
The procedure for expressions is "nbe" and the procedure for types is "nbe_ty".


##### Completeness

The PER model (Section 4.1) is defined in the Coq file "theories/Core/Semantic/PER/Definitions.v".
This consists of several definitions:
- The PERs Ne, Nf, and Typ (Figure 7) correspond to the definitions "per_bot", "per_top", and "per_top_typ", respectively;
- The PER Neu (Figure 7) corresponds to the definition "per_ne";
- The PER Nat (Figure 7) corresponds to the definition "per_nat";
- The PER for sorts (Figure 7) corresponds to the definition "per_sort_elem".
  To define "per_sort_elem", we first define a more abstract version "per_sort_elem_core" that leverages impredicativity.
- The PER for types (Figure 7) corresponds to the definition "per_typ_elem";
- The PER for contexts corresponds to the definition "per_ctx_env";
- The semantic subtyping relation (Figure 8) corresponds to the definitions "per_subtyp_sorted" (for the sorted one) and "per_subtyp" (for the general one);
- The context subtyping relation corresponds to the definition "per_ctx_subtyp".


The logical relations for completeness (Section 4.1.2) are defined in the Coq file "theories/Core/Completeness/LogicalRelation/Definitions.v".
This consists of several definitions:
- For equality of expressions, the definition "rel_exp_under_ctx_unsorted";
- For well-formed expressions, the definition "valid_exp_under_ctx_unsorted";
- For equality of types, the definition "rel_typ_under_ctx";
- For well-formed types, the definition "valid_typ_under_ctx";
- For subtyping, the definition "subtyp_under_ctx";
- For equality of substitutions, the definition "rel_sub_under_ctx";
- For well-formed substitutions, the definition "valid_sub_under_ctx".


##### Soundness

The gluing model (Section 4.2.1) is defined in the Coq file "theories/Core/Soundness/LogicalRelation/Definitions.v".
This consists of several definitions:
- The gluing relations associated to neutral types (Figure 9) correspond to "neut_glu_typ_pred" (type relation) and "neut_glu_exp_pred" (expression relation);
- The gluing relations associated to natural numbers (Figure 9) correspond to "nat_glu_typ_pred" (type relation) and "nat_glu_exp_pred" (expression relation);
- The gluing relations associated to function spaces (Figure 9) correspond to "pi_glu_typ_pred" (type relation) and "pi_glu_exp_pred" (expression relation);
- The gluing relation for sorts (Figure 10) correspond to "glu_sort_elem" (functional relation).
  Like for the PER model, it is defined in terms of a more abstract "glu_sort_elem_core" to leverage impredicativity.
- The gluing relation for types (Figure 10) correspond to "glu_typ_elem" (functional relation);
- The gluing relation for contexts correspond to "glu_ctx_env" (functional relation);
- The gluing relations Ne, Nf, and Typ correspond to "glu_elem_bot_unsorted", "glu_elem_top_unsorted", and "glu_typ_top_unsorted", respectively.


The logical relations for soundness (Section 4.2.2) are defined in the Coq file "theories/Core/Soundness/LogicalRelation/Definitions.v".
It consists of several definitions:
- The relation for well-formed contexts correspond to "glu_rel_ctx";
- The relation for well-formed substitutions correspond to "glu_rel_sub";
- The relation for well-formed expressions corresponds to "glu_rel_exp_unsorted";
- The relation for well-formed types corresponds to "glu_rel_typ_unsorted".



#### Algorithmic definitions

The algorithmic subtyping judgments (Section 5.1) are defined in the Coq file "theories/Algorithmic/Subtyping/Definitions.v".
It consists of two definitions:
- Subtyping for normal forms corresponds to "alg_subtyping_nf";
- Subtyping for arbitrary expressions corresponds to "alg_subtyping".

The algorithmic typing judgments (Section 5.2) are defined in the Coq file  "theories/Algorithmic/Typing/Definitions.v".
It consists of three mutual definitions:
- Type checking corresponds to "alg_type_check";
- Type inference corresponds to "alg_type_infer";
- Type well-formedness corresponds to "alg_wf_type".
