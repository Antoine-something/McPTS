## Evaluation instructions

### Step 1: Compilation (Optional)

__\*Warning\*__ 
Compilation takes a long time, up to ~30 minutes using four relatively recent i7 cores.
It also occasionally seems stuck (e.g. on "theories/Core/Soundness/NatCases.v"), but it is not.
To alleviate this for the artifact evaluation, we gave a VM image with the codebase pre-compiled.

Part of checking the validity of Coq code is making sure that it type checks, so we understand that some reviewers may want to do it themselves.
To this end, you can run the following two commands:

```
make clean
make
```


### Step 2: Run coqchk

`coqchk` goes through a compiled Coq file and tells which axioms are used (admitted results are counted as axioms) and whether non-standard features are used.
We have included a script that goes through all the Coq files, which you can run as follows:


```
./check.sh
```

The output is very long since it lists every file, but it ends with a summary of the findings.
It should be as follows:

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

