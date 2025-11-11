# Borrowing from Session Types

This directory contains the Agda formalization of decidability and soundness of
the algorithmic typing from the paper *Borrowing from Session Types* submitted
to the conference *OOPSLA'25*.

## Docker

We provide a docker image that comes with a compatible Agda and `agda-stdlib` version.

To typecheck the formalization first enter the docker image with an interactive shell:
(User of docker desktop on MacOS have to replace `docker-compose` with
`docker compose`!)

```bash
docker-compose build
docker-compose run -it bst-agda-algorithmic-typing bash
```

Then run the following commands:

```bash
agda BGV/Soundness.agda
agda BGV/Decidability.agda
```

Typechecking `BGV/Decidability.agda` may take a bit of time (13 minutes on my
desktop machine).

## Manual Installation

The project was developed with Agda 2.7.0.1, and `agda-stdlib` version 2.2.

While Agda can be run from the commandline, we recommend using it with the
emacs mode or the vscode plugin. More information can be found on:
https://agda.readthedocs.io/en/latest/getting-started/installation.html

## Contents

The supplementary material consists of a formalization of the logical and
algorithmic typing relations presented in the paper. The following properties
of interest are proved:

1.  Soundness of the algorithmic typing with respect to the logical typing.
    This is proved in in the file
    `BGV/Soundness.agda`
    in the theorem `soundness` at the end of the file.

2.  Decidability of the algorithmic typing. This is proved in the file
    `BGV/Decidability.agda`
    in the theorems `infer` and `check` at te end of the file.

    Unfortunately, the decidability proof seems to be a true stress test for
    Agda and takes 13 minutes to typecheck on my desktop machine.
    Please be patient!

The formalization differs from the presentation in the paper in the following ways:

- It models binary sum and choice types instead of n-ary sum and choice types.
  This difference is superficial, because n-ary sum and choice types can be
  encoded as binary sum and choice types.

- It uses an older version of the translation from algorithmic to logical
  expressions, which behaves functionally identical (replacing borrows by adding
  let-split bindings around expressions with multiple subexpressions), but is
  defined on algorithmic typing derivations instead of algorithmic terms. This is
  because originally, we had the `split` constant of the logical system annotated
  with the prefix session, which it should split off, so we needed the typing
  derivation to retrieve the types at which variables are borrowed, such that the
  translation can annotate the `split`s, which it introduces. As this is not the
  case anymore, we formulated the translation directly on algorithmic expressions
  in the paper, because this is easier to read and allowed us to present the
  translation before the algorithmic typing relation.

## Overview

The following outlines the module hierarchy of the formalization in the `BGV`
subdirectory:

-   `Types.agda`                       Definition of the type syntax used by both the algorithmic and
                                       the logical system.

-   `Expression.agda`                  Definition of the expression syntax. A single indexed type is
                                       used to describe both logical and algorithmic expressions,
                                       i.e. `Expr alg` for algorithmic and `Expr log` for logical.

-   `Algorithmic.agda`                 Definition of the algorithmic typing relation.

-   `Logical.agda`                     Definition of the logical typing relation.

-   `Translation.agda`                 Translation from typed algorithmic expressions to logical
                                       expressions.

-   `Decidability.agda`                Proof of decidability of algorithmic typing.

-   `Soundness.agda`                   Proof of soundness of algorithmic typing with respect to the
                                       logical typing.

-   `Determinstic.agda`                Proof that the algorithmic typing relation is deterministic.
                                       Used as a lemma for decidability of algorithmic typing.

-   `Multiplicities.agda`              Definitions and proofs about multiplicities (unrestricted,
                                       linear, left-ordered, right-ordered)

-   `Effect.agda`                      Definitions and proofs about effects (pure `0` and impure `1`)

-   `Ren.agda`                         Renamings used to rename variables in contexts, e.g.
                                       by the `split-ctx` operation.

-   `UsageMap.agda`                    Usage maps to track which parts of session types have been
                                       actually used (the `u` index in the algorithmic typing 
                                       relation)

-   `Id.agda`                          Definition of identifiers. Note that while we use natural
                                       numbers to represent identifiers, we use them as names
                                       and not as DeBruijn indicies.

-   `Context.agda`                     Typing contexts. Reexports the definitions from
                                       `Context/*.agda`.

-   `Context/Syntactic.agda`           Definitions and proofs about syntactic typing contexts, i.e.
                                       trees in the style of bunched implications.

-   `Context/Semantic.agda`            Definitions and proofs about semantic typing contexts, i.e.
                                       pairs of graphs and sets.

-   `Context/Pattern.agda`             Definitions and proofs about typing context patterns, i.e.
                                       syntactic typing contexts with a hole.

-   `Context/SyntacticSplit.agda`      Definitions and proofs about the typing context
                                       decomposition, i.e. the `↓ᶜ` operator, which given a context
                                       `Γ` and set of variables `X`, tries to find a context pattern
                                       `𝒢` and a context `Γ` such that `Γ ≲ 𝒢 [ Γ' ]` where
                                       `Γ` contains only bindings for variables from `X`, and
                                       `𝒢` contains only bindings for variables not in `X`.

-   `Split.agda`                       Definitions and lemmas around the context splitting operations
                                       required to deal with borrowing, e.g. the splitting of
                                       bindings `x : s₁;s₂` into two bindings `x₁ : s₁` and `x₂ : s₂`.

-   `SplitTyping.agda`                 Lemmas about the interaction of the operations from `Split.agda`
                                       with the algorithmic typing relation.

-   `Util/Closures.agda`               Reflexive, transitive, and symmetric closures of binary
                                       relations.

-   `Util/Decidable.agda`              Type classes for decidable equality

-   `Util/Graph.agda`                  Definitions and proofs about directed, acyclic graphs

-   `Util/List.agda`                   Definitions and proofs about lists and finite sets described
                                       as a setoid over lists.

-   `Util/Map.agda`                    Definitions and proofs about finite maps as association lists.

-   `Util/FunMap.agda`                 Definitions and proofs about maps as functions. This is used
                                       as a basis for renamings and usage maps.

## Postulates

Our formalization postulates a single theorem, which is a standard result from
graph theory, but out of scope from this paper:

    _≲ᵍ?_  : ∀ {ℓ} {L : Set ℓ} → (g₁ g₂ : G.Graph L) → Dec (g₁ ≲ᵍ g₂)

This theorem states that for two finite, directed, acyclic graphs g₁ and g₂, it
is decidable whether g₁ has the same nodes and a subset of the edges of g₂ up to
isomorphism.

The postulate can be found in `BGV/Context/Semantic.agda`.

