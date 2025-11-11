open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Context {M : OPM} (DM : DecidableOPM M) where

open import LawAndOrder.Context.Semantic DM public
open import LawAndOrder.Context.Syntactic DM public
open import LawAndOrder.Context.Context DM public
