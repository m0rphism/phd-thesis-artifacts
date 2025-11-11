module LawAndOrder.Id where

open import Data.String as String using (String)
open import Data.List using (List; []; _∷_)

Id = String

variable
  x y z x' y' z' : Id
  xs ys zs xs' ys' zs' : List Id
