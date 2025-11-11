# Law and Order for Typestate with Borrowing

This directory contains the supplementary material for the paper
*Law and Order for Typestate with Borrowing* submitted to the
conference OOPSLA'24.

## Dependencies

The project requires Agda 2.6.4 or 2.6.5, and the `agda-stdlib` version 2.0.

While Agda can be run from the commandline, we recommend using it with
the emacs mode or the vscode plugin. More information can be found on:
https://agda.readthedocs.io/en/latest/getting-started/installation.html

## Contents

The supplementary material consists of a formalization of the logical
and algorithmic typing relations presented in the paper. The following
properties of interest are proved:

1.  Soundness of the algorithmic typing with respect to the logical
    typing. This is proved in in the file
    `LawAndOrder/Algorithmic/TypingSoundness.agda`
    in the theorems `soundness↑` and `soundness↓`.

2.  Decidability of the algorithmic typing. This is proved in the file
    `LawAndOrder/Algorithmic/TypingDecidable.agda`
    in the theorems `infer` and `check`.

The following outlines the module hierarchy of the formalization in
the `LawAndOrder` subdirectory:

-   `Algorithmic/Expression.agda`      Definition of the surface syntax

-   `Algorithmic/Typing.agda`          Definition of the algorithmic typing relation

-   `Algorithmic/TypingDecidable.agda` Proof of decidability of algorithmic typing

-   `Algorithmic/TypingSound.agda`     Proof of soundness of algorithmic typing

-   `Context.agda`                     Reexports the definitions from `Context/*.agda`

-   `Context/Context.agda`             Definitions and proofs about context-contexts

-   `Context/Semantic.agda`            Definitions and proofs about the semantic context

-   `Context/Syntactic.agda`           Definitions and proofs about the syntactic context

-   `Context/SyntacticSplit.agda`      Definitions and proofs about the context decomposition

-   `Effect.agda`                      Definitions and proofs about the effects 0 and 1

-   `Id.agda`                          Definition of identifiers

-   `Logical/Expression.agda`          Definition of the internal syntax

-   `Logical/Typing.agda`              Definition of the logical typing relation

-   `Multiplicities.agda`              Definition of multiplicities (unrestricted,
                                       linear, left-ordered, right-ordered)

-   `Type.agda`                        Definition of the type syntax

-   `Util/Closures.agda`               Reflexive, transitive, and symmetric closures
                                       of binary relations

-   `Util/Decidable.agda`              Type classes for decidability

-   `Util/Graph.agda`                  Definitions and proofs about directed, acyclic graphs

-   `Util/List.agda`                   Definitions and proofs about lists and sets

-   `Util/OrderedPartialMonoid.agda`   Definition of Ordered Partial Monoids (OPM) and
                                       its decidability.

## Postulates

The formalisation postulates the following theorem, which is a standard result from
graph theory, but out of scope from this paper:

    _≲ᵍ?_  : ∀ {ℓ} {L : Set ℓ} → (g₁ g₂ : G.Graph L) → Dec (g₁ ≲ᵍ g₂)

This theorem states that for two finite, directed, acyclic graphs
g₁ and g₂, it is decidable whether g₁ has the same nodes and a subset
of the edges of g₂ up to isomorphism.

The postulate can be found in `LawAndOrder/Context/Semantic.agda`.


