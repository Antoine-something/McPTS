# List of key definitions


## PTS* signatures

Definitions relevant to PTS* signature are located in the folder "theories/PtsSignature".
There are four main definitions:
- PTS* signatures themselve (Definition 2.1) are defined in the Coq file "theories/PtsSignature/Signatures.v", as the record "PtsSig".
- Predicativity of signatures (Definition 2.2) is defined in the Coq file "theories/PtsSignature/Predicativity.v", as the record "PredicativeSig"
- Functionality of signatures (Definition 2.3) is defined in the Coq file "theories/PtsSignature/Functionality.v", as the record "FunctionalSig"
- Decidability of signatures (Definition 2.4) is defined in the Coq file "theories/PtsSignature/Decidability.v", as the record "DecidableSig"


## Declarative definitions

### Syntactic definitions

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


Weakening substitutions (Section 4.2.1) of an arbitrary PTS* are define in the Coq file "theories/Core/Soundness/Weakening/Definitions.v".


### Semantic definitions




## Algorithmic definitions


## Case studies





# List of claims

## Generic properties for arbitrary signatures

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


## Normalization for predicative signatures

### Completeness of NbE

Functionality of the PERs (mentionned in text, section 4.1) has three parts:
- Functionality of the PER for sorts: the lemmas "per_sort_elem_right_irrel", "per_sort_elem_left_irrel", and "per_sort_elem_cross_irrel" in the Coq file "theories/Core/Semantic/PER/Lemmas.v"
- Functionality of the PER for types: the lemmas "per_typ_elem_right_irrel", "per_typ_elem_left_irrel", and "per_typ_elem_cross_irrel" in the Coq file "theories/Core/Semantic/PER/Lemmas.v"
- Functionality of the PER for contexts: the lemmas "per_ctx_env_right_irrel", "per_ctx_env_left_irrel", and "per_ctx_env_cross_irrel" in the Coq file "theories/Core/Semantic/PER/Lemmas.v"


Theorem 4.1 (Realizability of the PER model): the lemma "realize_per_typ_elem_gen" in the Coq file "theories/Core/Semantic/Realizability.v"


Theorem 4.2 (Fundamental theorem of completeness): the theorem "completeness_fundamental" in the Coq file "theories/Core/Completeness/FundamentalTheorem.v".  Since this is a very large proof, most of the individual cases are proven separately in the corresponding files of the "theories/Core/Completeness" folder (e.g. the cases for functions are in the Coq file "theories/Core/Completeness/FunctionCases.v")


Corollary 4.3 (Completeness of normalization): the theorem "completeness" in the Coq file "theories/Core/Completeness.v"


### Soundness of NbE


Functionality of the gluing relations (Section 4.2.1) has two parts:
- Functionality of the gluing relations for sorts: the lemma "functional_glu_sort_elem" in the Coq file "theories/Core/Soundness/LogicalRelation/CoreLemmas.v"
- Functionality of the gluing relations for types: the lemma functional_glu_typ_elem" in the Coq file "theories/Core/Soundness/LogicalRelation/CoreLemmas.v"
- Functionality of the gluing relations for contexts: the corollary "functional_glu_ctx_env" in the Coq file "theories/Core/Soundness/LogicalRelation/Lemmas.v"


Theorem 4.4 (Realizability of the gluing model): the theorem "realize_glu_typ_elem_gen" in the Coq file "theories/Core/Soundness/Realizability.v"


Theorem 4.5 (Fundamental theorem of soundness):
- For annotated judgments: the theorem "soundness_fundamental" in the Coq file "theories/Core/Soundness/FundamentalTheorem.v"
- For ordinary judgents: the theorems "soundness_fundamental_ctx", "soundness_fundamental_exp", "soundness_fundamental_typ", and "soundness_fundamental_sub" in the Coq file "theories/Core/Soundness/FundamentalTheorem.v"


Theorem 4.6 (Soundness of normalization): the theorem "soundness" in the Coq file "theories/Core/Soundness.v"


## Algorithmic type checking for predicative and functional signatures


Theorem 5.1 (Equivalence of algorithmic and declarative subtyping):
- Soundness of algorithmic subtyping for normal types: the lemma "alg_subtying_nf_sound" in the Coq file "theories/Algorithmic/Subtyping/Lemmas.v"
- Completeness of algorithmic subtyping: the lemma "alg_subtyping_complete" in the Coq file "theories/Algorithmic/Subtyping/Lemmas.v"
- Soundness of algorithmic subtyping for arbitrary types: the lemma "alg_subtyping_sound" in the Coq file "theories/Algorithmic/Subtyping/Lemmas.v"


Theorem 5.2 (Soundness of algorithmic typing): the lemma "alg_type_sound" in the Coq file "theories/Algorithmic/Typing/Lemmas.v"


Theorem 5.3 (Completeness of algorithmic typing): the lemma "alg_type_complete" in the Coq file "theories/Algorithmic/Typing/Lemmas.v".  Note this lemma has several trivial parts (implications of True), which are needed to use the mutual induction principle of the judgments.



## Extraction of verified type checkers for predicative, functional, and decidable signatures


This section does not have any formal claims, but the ability to extract type checkers is the central claim of the paper, so it deserves a discussion.  The crucial part of the extraction is to provide a functional implementation of our judgments in Coq.  This is done across the several files in "theories/Extraction", e.g. "theories/Extraction/TypeCheck.v" implements the algorithmic type checking judgment.

The extraction itself is enabled in the case studies (folder "theories/CaseStudies"), by extracting the "main" function of the corresponding "Entrypoint.v" file (e.g. "theories/CaseStudies/LF/Entrypoint.v").  Each case study has a generated parser and a "Frontend.v" file that performs elaboration from a surface language to our internal representation.  The "main" function basically invokes the generated parser, performs elaboration, and calls the type checker.