# agda-prefix-stripping

The directory `agda-prefix-stripping` contains the Agda formalization of decidability, soundness and
completeness of the prefix stripping algorithm for session types presented in the paper *Borrowing
from Session Types* submitted to the conference *OOPSLA'25*.

This artifact is concerned with Section 4.3 “Prefix Stripping” providing mechanized proofs.


## Docker

We provide a Dockerfile with a compatible Agda and agda-stdlib.

First build the image. From inside the directory `agda-prefix-stripping` run

```bash
docker build . -t bst-prefix-stripping
```

To typecheck the mechanized proofs run

```bash
docker run -it bst-prefix-stripping agda PrefixStripping/Decide.agda
```


## Manual Installation

The project was developed with Agda 2.7.0.1, and agda-stdlib version 2.2.

While Agda can be run from the commandline, we recommend using it with the
emacs mode or the vscode plugin. More information can be found on:
https://agda.readthedocs.io/en/latest/getting-started/installation.html


## Proof Outline

This part of the artifact is concerned with section 4.3 “Prefix Stripping” and depends on the
definitions for session types (borrowed and owned) and type composition given in section 3.1
“Syntax”.

```agda
-- Defines basic syntactic constructs.
import PrefixStripping.Syntax

-- Defines session types, substitution on session types, and type composition.
import PrefixStripping.Sessions

-- Defines equivalence of session types.
import PrefixStripping.Sessions.Equivalence

-- Proves that the set of syntactic subterms of all session types is finite.
import PrefixStripping.Sessions.Subterm

-- Supporting definitions for the decision procedure.
import PrefixStripping.Decide.Universe

-- Main workhorses for the soundness proofs.
import PrefixStripping.Decide.Soundness

-- Using the lemmas about syntactic subterms and Data.List.Countdown from
-- agda-stdlib this provides machinery proving that the algorithm terminates.
import PrefixStripping.Decide.Coinduction

-- Contains the prefix stripping algorithm and the final proofs.
import PrefixStripping.Decide
```


## Differences to the paper

* _No priorities._ The stripping algorithm is not concerned with the priorities of session
  types. The formalization thus does not include priority annotations.

* _Combined constructors for dual operations._ The dual constructors for send/receive and
  internal/external choice receive the same treatment, respectively. Thus we combine them into two
  constructors parameterized by a direction `Dir`.

* _One datatype combining owned and borrowed sessions._ The only syntactic difference between owned
  and borrowed sessions is in their terminating constructors (`Close` and `Wait` vs `Return`). The
  formalizations combines owned and borrowed sessions into one datatype `𝕊` parameterized by a type
  `END`. Most operations and lemmas are defined over session types with arbitrary `END` types.
  
  Instantiating `END` with `Dir` is equivalent to session types with `Close`/`Wait`; instantiating
  with `⊤` is equivalent to borrowed session types. This instantiation is aliased as `ℙ` (read
  “prefix”/“prefix session type”). Metavariables named `r` or similar refer to the _result_ or
  _remainder_ of the stripping algorithm.


## Mechanized definitions and results

| Definition / Theorem                         | Paper           | File                        | Formalization                                                  |
|----------------------------------------------|-----------------|-----------------------------|----------------------------------------------------------------|
| Session types                                | Fig. 3, p. 10   | `Sessions.agda`             | `data 𝕊`                                                       |
| Session type composition                     | Sec. 3.1, p. 10 | `Sessions.agda`             | `_◇_`                                                          |
| Equi-recursive equivalence of session types  |                 | `Sessions/Equivalence.agda` | `_≃_` (*)                                                      |
| "`Return` appears in …"                      |                 | `Sessions/Equivalence.agda` | `∃□`                                                           |
| Stripping relation                           | Fig. 11, p. 19  | `Decide/Universe.agda`      | `data _⊢_%_=_`                                                 |
| Decidability of Stripping                    | Thm. 4.1, p. 19 | `Decide.agda`               | `strip`                                                        |
| Stripping Finite Prefixes                    | Thm. 4.2, p. 19 | `Decide.agda`               | `finite-⊥⇒¬∃□`, `finite-¬⊥⇒∃□`, `finite-∃□⇒¬⊥`, `finite-¬∃□⇒⊥` |
| Completeness of Stripping                    | Thm. 4.3, p. 20 | `Decide.agda`               | (1) `complete-∃□`, (2) `complete-¬∃□`                          |
| Soundness of Stripping                       | Thm. 4.4, p. 20 | `Decide.agda`               | (1) `sound-S`, (2) `sound-⊥`                                   |

NB: the symbols in the second part of `PrefixStripping/Decide.agda` are quantified over `⊢p` (the
prefix to strip) and `⊢s` (the session we are stripping from) using module parameters.

`_≃_` models equi-recursive session type equivalence (ie. recursive session types are equivalent to
their unfolding). We chose an approximation of coinductive equivalence that works using purely
inductively defined types and functions. `⟦_⟧` unfolds a session type and builds an interaction tree
up to a given depth. Two session types are then called equivalent if the trees are equal for any
given depth


## Postulates

Our mechanization postulates a single theorem:

```
_ = PrefixStripping.Sessions.Equivalence.Decide._≃?_
```

The theorem states that if the equality of base types is decidable then the equivalence of session
types is decidable. This is a well established result. Algorithmically it follows very much the
structure of prefix stripping with different base cases.

You can check that there are no other postulates by running the following command. It should list
only the single postulate described above.

```sh
docker run -it bsession/prefix-stripping grep -r postulate PrefixStripping/
```
