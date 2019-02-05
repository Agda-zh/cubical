{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Base where

open import Cubical.Core.Everything

open import Cubical.Data.Sum
open import Cubical.Data.Unit

record Conat : Set
Prev = Unit ⊎ Conat
record Conat where
  coinductive
  constructor conat
  field prev : Prev

pattern zero  = inl tt
pattern suc n = inr n
