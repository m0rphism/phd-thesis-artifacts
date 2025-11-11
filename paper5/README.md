# Abstractions for Multi-Sorted Substitutions

This directory contains the supplementary material for the paper
*Abstractions for Multi-Sorted Substitutions* submitted to the
conference ITP'24.

## Contents

The supplementary material consists of two separate Agda projects:

-   The `Simple` subdirectory contains the simplified framework as
    presented in the Paper. The file `Kits.agda` contains the complete
    framework, the file `SystemF.agda` uses the framework to prove
    subject reduction for System F, and the file `Generics.agda`
    contains the generic description of the object languages that the
    reflection algorithm from the `Full` framework can handle.

-   The full framework can be found on https://github.com/m0rphism/kitty
    and includes our case studies.
    
    The full framework is significantly more involved and provides
    
    -    Representation independence for substititions, i.e.
         Substitutions can not only represented as functions but also
         as indexed lists or syntacticly.

    -    Representation independence for typing contexts, i.e.
         Typing contexts can not only represented as functions but also
         as indexed lists.

    -    A reflection algorithm to derive all instantiations for
         untyped substitution.

    -    Heterogenous equality for maps, which allows to compare
         maps from different Kits, e.g. renamings with substitutions.
         
    As the implementation is currently still very much in flux,
    there is very little documentation. However looking at the syntax
    definitions of the case studies might still be instructive.
    
    The case studies are located in the repository in `src/Kitty/Examples` and
    consist of:
    
    -    A formalization of System F can be found in the
         `SystemF` subdirectory. Compared to the formalization
         from our paper, it uses the reflection mechanism to derive
         everything except type preservation.

    -    A formalization of System F with subtyping can be found in the
         `SystemFSub` directory.

    -    A formalization of lambda calculus with pi types can be found
         in the `LambdaPi` directory.

         The formalization is a bit messy, as we are not yet very much
         experienced with mechanized metatheory of dependent types.
         However, the reflection mechanism works and type preservation
         can be proven nicely with our `TypingTraversal` abstraction,
         which is the main point of this case study.

    -    A formalization of simply typed lambda calculus with pattern
         matching for product, sum and unit types can be found in the
         `Patterns` subdirectory.

## Dependencies

The formalization in the `Simple` subdirectory requires only the Agda
standard library and has been tested with Agda version 2.6.2, 2.6.3,
2.6.4, and 2.6.5.

The formalization of the full framework requires Agda 2.6.4 or 2.6.5,
and the `agda-stdlib` version 2.0.

While Agda can be run from the commandline, we recommend using it with
the emacs mode or the vscode plugin. More information can be found on:
https://agda.readthedocs.io/en/latest/getting-started/installation.html

