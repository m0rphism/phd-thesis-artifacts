# Typed Translation from VGR to GV

Artifact for the paper "Relating Functional and Imperative Session Types"
Hannes Saffrich, Peter Thiemann
https://arxiv.org/abs/2010.08261

Imperative session types provide an imperative interface to session-typed communication in a functional language. Compared to functional session type APIs, the program structure is simpler at the surface, but typestate is required to model the current state of communication throughout.
Most work on session types has neglected the imperative approach. We demonstrate that the functional approach subsumes previous work on imperative session types by exhibiting a typing and semantics preserving translation into a system of linear functional session types.
We further show that the untyped backwards translation from the functional to the imperative calculus is semantics preserving. We restrict the type system of the functional calculus such that the backwards translation becomes type preserving. Thus, we precisely capture the difference in expressiveness of the two calculi.

## System Requirements

The formalization was tested with

* Agda version 2.6.1.3 and Agda standard library version 1.6

* Agda version 2.6.2 and Agda standard library version 1.7

## Directory Structure

The subdirectory VGR contains definitions of syntax and typing for VGR, along with properties of the operators involved. A lot of machinery is needed to deal with guaranteeing that channel names in stores are unique and to deal with the disjointness of stores in general. 

The subdirectory GV defines syntax and typing for GV.

File Translate.agda in the main directory defines the translation and proves that it preserves typing.
Our proof makes a few assumptions.

## Remarks

* As we use a very simple model of variable binding (the one from Wadler and Kokke's PLFA book), we reserve some variable names for the translation and assume they are not used in subject programs. This is postulated as `post-st-unused`.

* We do not prove a simple lemma `post-swap-expr` about swapping typing assumptions for different variable names. This is a standard result with detailed proofs in PLFA.

* Stores are modeled like records with all distinct field names. We generally assume that the order of fields does not matter, though most of the time our definitions also preserve this ordering. The only place where we need implicit reordering of fields is in the typing preservation proof for the translation of the let expression. We can only prove the desired result up to reordering, which is expressed by a predicate `⊆⊇`. To proceed without generating an explicit reordering of the fields we postulate equality up to reordering:

      ⊆⊇-≡ : {σ₁ σ₂ : Store} → σ₁ ⊆⊇ σ₂ → σ₁ ≡ σ₂

* A final proof obligation that's missing is an obvious statement about disjointness and intersection: if two stores  `σ₁` and `σ₁′`  are disjoint - expressed by `all# σ₁ σ₁′`, then their intersection with any other store `σ₂` is also disjoint.

      all# σ₁ σ₁′ → all# (σ₁ ∩ σ₂) (σ₁′ ∩ σ₂)

* In contrast to the paper, the GV formalization supports no explicit closing of channels, but defines channels of session type `End` to be unrestricted, so they can simply be dropped. This is due to historic reasons and adding an explicit `close` construct to GV would not cause any problems.
