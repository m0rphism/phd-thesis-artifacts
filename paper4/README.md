# Borrowing from Session Types (Artifact)

## Introduction

This artifact contains mechanized proofs and implementations
supporting the paper  *Borrowing from Session Types* submitted
to *OOPSLA'25*.

It has four parts corresponding to subdirectories. 
Each subdirectory contains its own readme file.

- `agda-algorithmic-typing`  Agda development (mechanized proof) for
  the algorithmic typing: decidability and soundness (section 4)
- `agda-prefix-splitting` Agda development (mechanized proof)
  supporting the prefix stripping algorithm: soundness, completeness, and decidability
  (section 4.3)
- `interpreter` Rust implementation of a prototype type checker and
  interpreter (section 4)
- `idris-encoding` Idris2 encoding of finite, non-branching
  session types with borrowing (Appendix B)
- `benchmark/` contains a Haskell project that evaluates the performance
  of our semantics as described in Section 4.5.

All technical claims of the paper are supported by mechanized proofs,
except the claim of typing preservation for the translation defined
and discussed in section 3.

## Hardware Dependencies

There are no known hardware dependencies. All software has been
dockerized and we checked that the packaged code runs on Linux and
MacOS (both Apple, and Intel silicon).

## Getting Started Guide

A working installation of docker is needed.

In each subdirectory, a docker container has to be built and executed.
(Some subdirectories contain instructions to build locally without docker.)

### Agda Algorithmic Typing

In directory `agda-algorithmic-typing`.

To typecheck the formalization first enter the docker image with an interactive shell:
(User of docker desktop on MacOS may have to replace `docker-compose` with
`docker compose`! Depending on your machine, this may take about 10 minutes.)

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
Running the commands prints a log of the files as they are
typechecked. Success means that no type errors are reported.

### Agda Prefix Stripping

The directory `agda-prefix-stripping` contains the Agda formalization of decidability, soundness and
completeness of the prefix stripping algorithm for session types presented in the paper *Borrowing
from Session Types* submitted to the conference *OOPSLA'25*.

This artifact is concerned with Section 4.3 “Prefix Stripping” providing mechanized proofs.

We provide a Dockerfile with a compatible Agda and agda-stdlib.

First build the image. From inside the directory `agda-prefix-stripping` run

```bash
docker build . -t bst-prefix-stripping
```

To typecheck the mechanized proofs run

```bash
docker run -it bst-prefix-stripping agda PrefixStripping/Decide.agda
```

### Haskell Benchmark

The directory `benchmark` contains the Haskell micro benchmark from Section 4.5 that
evaluates the performance of our semantics.

#### Kick the tires

The following uses docker to enters an interactive `bash` shell where the
benchmark has been already compiled:

```bash
docker-compose build
docker-compose run bst-benchmark
```

The following commands can then be used in the interactive shell to run the
benchmarks:

```bash
stack run --
```

### Interpreter

The directory `interpreter` contains an implementation of a
typechecker and interpreter for the language from the paper 
*Borrowing from Session Types*.

The implementation supports all features mentioned in the paper and additionally
supports the following features:

- unrestricted base types `String`, `Int`, and `Bool` with the usual operations;

- unrestricted function types;

- recursive function definitions and recursive session types;

- irrefutable pattern matching in let expressions for products;

- a function that prints to stdout.

Note that the `spawn` expression differs from the paper in that it is
call-by-need, and hence does not require you to wrap its subexpression in a
lambda, e.g. instead of `spawn (λ(). e)` you can directly write `spawn e`.

#### Kick the tires

1.  Build the image via

    ```bash
    docker-compose build
    ```

2.  Run the image via

    ```bash
    docker-compose run bst-interpreter
    ```

    This drops you into an interactive bash shell, where the compiled
    interpreter `bsti` is already on the `PATH`.

3.  Typecheck and interpret a program via e.g.

    ```bash
    bsti examples/example-simple.bgv
    ```

    The current host directory is mounted into the current guest directory, so
    it is possible to change or add examples on the host without having to
    rebuild the image.


### Idris Encoding

The directory `idris-encoding` contains an encoding of borrowed
session types in Idris2 version 0.7.0 as outlined in Appendix B of the
paper. This implementation does not support branching (which can be
emulated) nor recursion. Indirectly, this type-checked implementation
supports our claim that the translation from section 3 is typing preserving.

When using docker execute the following commands.

```sh
> docker build -t bst-idris . # takes a while ...
> docker run -it bst-idris sh
# sh compile.sh
1/4: Building Linear (Linear.idr)
2/4: Building LinearUnion (LinearUnion.idr)
3/4: Building Sessionx (Sessionx.idr)
4/4: Building Splittablex (Splittablex.idr)
# 
```

Voila! The encoding of borrowed session types compiled successfully.


## Step by Step Instructions


### Agda Algorithmic Typing

Here is some more information for taking a deeper dive into this part
of the artifact.

#### Contents

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


#### Overview

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

#### Postulates

Our formalization postulates a single theorem, which is a standard result from
graph theory, but out of scope from this paper:

    _≲ᵍ?_  : ∀ {ℓ} {L : Set ℓ} → (g₁ g₂ : G.Graph L) → Dec (g₁ ≲ᵍ g₂)

This theorem states that for two finite, directed, acyclic graphs g₁ and g₂, it
is decidable whether g₁ has the same nodes and a subset of the edges of g₂ up to
isomorphism.

The postulate can be found in `BGV/Context/Semantic.agda`.


### Agda Prefix Stripping

#### Proof Outline

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


#### Differences to the paper

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


#### Mechanized definitions and results

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


#### Postulates

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


### Interpreter

Here is some more information about the interpreter.
There is a bunch of examples in the `examples` subdirectory, including
all examples from the paper. Note that some of the examples contain
type errors on purpose; these are located in `examples/negative`.

#### Syntax

The following grammar describes the complete, concrete syntax supported by the interpreter.
For readability, operator precedence, associativity and whitespace are omitted.

```
Multiplicities
m ::= 'u' | 'unr'                   (unrestricted)
    | 'p' | 'lin'                   (linear/"parallel")
    | 'l' | 'left'                  (left ordered)
    | 'r' | 'right'                 (right ordered)

Effects
E ::= '0'                           (pure)
    | '1'                           (impure)

Types
t ::= t '-[' m ';'? E ']->' t       (function type)
    | t '*[' m ']' t                (product type)
    | '<' (l ':' t ',')* '>'        (variant type)
    | 'Chan'? s                     (session type)
    | 'Unit'                        (unit type)
    | 'Int'                         (64bit signed integer type)
    | 'Bool'                        (boolean t type)
    | 'String'                      (unicode string type)

Session Types
s ::=  '!' t '.' so                 (sending session type)
     | '?' t '.' so                 (receiving session type)
     | '+{' (l ':' s ',')* '}'      (internal choice type)
     | '&{' (l ':' s ',')* '}'      (external choice type)
     | 'Close'                      (sending end of protocol of owned session)
     | 'Wait'                       (receiving end of protocol of owned session)
     | 'Return'                     (end of protocol of borrowed session)
     | 'mu' x '.' s                 (recursive session type)
     | x                            (session variable)

Expressions
e ::= x                             (variable)
    | '\' x '.' e                   (lambda abstraction)
    | e e                           (unr/lin/right function application)
    | e '|>' e                      (left function application with flipped arguments)

    | 'let' x '=' e 'in' e          (let expression)
    | e ';' e                       (sequencing)

    | '(' e ',' e ')'               (pairs)
    | 'let' x ',' x '=' e 'in' e    (product elimination)

    | 'inj' l e                     (variant introduction)
    | 'case' e '{'                  (variant elimination)
        (l x '->' '{' e '}')*
      '}'

    | 'let' x ':' t '\n'
            x p+ '=' e 'in' e       (let expression for recursive function
                                     with irrefutable pattern matching clauses)

    | 'fork' e                      (thread spawning)
    | 'new' s                       (channel allocation)
    | 'send' e1 e2                  (channel send operation)
    | 'recv' e                      (channel receive operation)
    | 'branch' e                    (external choice operation)
    | 'select' l e                  (internal choice operation)
    | 'drop' e                      (elimination of borrowed channels)
    | 'close' e                     (elimination of owned channels)
    | 'wait' e                      (elimination of owned channels)
    | '&' x                         (borrow)

    | 'true' | 'false'              (boolean introduction)
    | 'if' e 'then' e 'else' e      (boolean elimination)
    | e '&&' e                      (boolean conjunction)
    | e '||' e                      (boolean disjunction)
    | '!' e                         (boolean negation)

    | 'unit'                        (unit introduction)

    | <str>                         (string literals)
    | e '+' e                       (string concatenation)
    | 'str' e                       (conversion to string)
    | 'print' e                     (printing to stdout)

    | <int>                         (integer literals)
    | '-' e                         (integer negation)
    | e '+' e                       (integer addition)
    | e '-' e                       (integer subtraction)
    | e '*' e                       (integer multiplication)
    | e '/' e                       (integer division)

    | e '<' e                       (comparison)
    | e '<=' e                      (comparison)
    | e '>' e                       (comparison)
    | e '>=' e                      (comparison)
    | e '==' e                      (equality)
    | e '!=' e                      (inequality)

    | e ':' t                       (type annotation)
    
Variables
x ::= [a-zA-Z_]+[a-zA-Z0-9_]*

Labels
l ::= [a-zA-Z_]+[a-zA-Z0-9_]*

Integer Literals
<int> ::= '-'? [0-9]+

String Literals
<str> ::= '"' [^"]* '"'             (strings like "foo")
        | '\'' [^"]* '\''           (strings like 'foo')
        | '\'\'\'' [^"]* '\'\'\''   (strings like '''foo''')

Patterns
p ::= x                             (variable pattern)
    | '(' p1 ',' p2 ')'             (pair pattern)
    
Program
P ::= e                             (main expression)
```

We also provide unicode alternatives for certain tokens:

- A lambda `\x. e` can also be written as `λx. e`

- A function type `t1 -[ m E ]-> t2` can also be written as `t1 –[ m E ]→ t2`

- An unordered product type `t1 *[ p ] t2` can also be written as `t1 ⊗ t2`

- A left-ordered product type `t1 *[ l ] t2` can also be written as `t1 ⊙ t2`

- A recursive session type `mu x. s` can also be written as `µ x. s`

Comments are started with a `#` and range until the end of the line.

#### Examples

The following shows the obligatory math server example:

```agda
let 
  server : ?Int.?Int.!Int.Wait -[ u 1 ]→ Unit
  server c =
    let x = recv &c in
    let y = recv &c in
    send (x + y) &c;
    wait c
in

let
  client : !Int.!Int.?Int.Close -[ u 1 ]→ Unit
  client c =
    send 1 &c;
    send 2 &c;
    print (recv &c);
    close c
in

let c1, c2 = new !Int.!Int.?Int.Close in
fork (server c2);
client c1
```

This example can also be written without the syntactic sugar for Haskell-style
function definitions, i.e. as simple `let`-expressions, where the body is
a lambda wrapped in a type annotation expression `(\c. …) : t`:

```agda
let 
  server = \c.
    let x = recv &c in
    let y = recv &c in
    send (x + y) &c;
    wait c
  : ?Int.?Int.!Int.Wait -[ u 1 ]→ Unit
in

let
  client = \c.
    send 1 &c;
    send 2 &c;
    print (recv &c);
    close c
  : !Int.!Int.?Int.Close -[ u 1 ]→ Unit
in

let c1, c2 = new !Int.!Int.?Int.Close in
fork (server c2);
client c1
```

Further examples, including the examples from the paper can be found in the
`examples` subdirectory.

### Idris Encoding

Here is a short description of the files in subdirectory `src`.

* `Linear.idr` patched version of the like-named file from the Idris2 library `linear`. Patches by the maintainer.
* `LinearUnion.idr` patched version of the library file `Data.OpenUnion.idr` adapted by us to accept linear types.
* `Sessionx.idr` patched version of the session library https://test.idris-lang.org/Idris2/linear/source/System.Concurrency.Session.html to accommodate transmitting linear types.
* `Splittablex.idr` our implementation of splittable channels as documented in the paper. The functions are named as in the paper and the remaining definitions are commented.

You are encouraged to write a server for the binary-operation protocol that
receives two numbers, sends a number, and stops.

### Haskell Benchmark

#### Overview

The benchmark runs 200 sessions where each session contains 1000 send and 1000
receive operations, the latter in a different thread (no session types, just
plain parametric channels). It sends the numbers 1..1000 and the receiver
calculates the sum. The benchmark has three modes:

- Prim: using simple synchronous channels

- Cell: using the cell encoding outlined in the paper, but optimized in the
  sequential parts as outlined in (A-Q1)

- Split: using the full cell encoding explained in the paper

Split and Cell are implemented using Prim as primitive channels.

#### Results

The results are shown in the table below and have been obtained by taking the
average wall clock time of 11 runs of the benchmark using the unix `time`
utility:

| Mode  | Time   | Overhead |
|-------|--------|----------|
| Prim  | 6.52 s |     0.0% |
| Cell  | 7.31 s |   ~11.9% |
| Split | 7.36 s |   ~12.7% |

We believe this overhead is negligible in practice as this micro benchmark is
communication bound and we expect a real program to be much more computation
bound.

## Reusability Guide

Reusable parts

* the proof artifacts are modularized and parts of them can be used
  independently.
* the interpreter showcases a bidirectional type checking algorithm,
  which can be used as a template for subsequent work.

## Changelog

- Added docker images for all supplements.
- Added the Haskell benchmark.
- Fixed bugs in typechecker implementation and added examples.
- Improved documentation.
- Completed mechanization of prefix stripping proof.

