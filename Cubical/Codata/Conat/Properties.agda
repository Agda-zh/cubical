{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Cubical.Data.Unit

open import Cubical.Core.Everything

open import Cubical.Codata.Conat.Base

open Conat

succ : Conat → Conat
succ a = conat (psuc a)

_+_ : Conat → Conat → Conat
pred (a + b) with pred a | pred b
... | pzero  | pzero  = pzero
... | pzero  | psuc y = psuc y
... | psuc x | pzero  = psuc x
-- Can't replace `conat ∘ psuc` with succ due to termination check
... | psuc x | psuc y = psuc (conat (psuc (x + y)))

Unwrap-pred : Pred Conat -> Set
Unwrap-pred  pzero   = Unit
Unwrap-pred (psuc _) = Conat

unwrap-pred : (n : Pred Conat) -> Unwrap-pred n
unwrap-pred  pzero   = _
unwrap-pred (psuc x) = x

private -- tests
  zero = conat pzero
  one  = succ zero
  two  = succ one

  succOne≡two : succ one ≡ two
  succOne≡two i = two

  predTwo≡one : unwrap-pred (pred two) ≡ one
  predTwo≡one i = one

  0+1≡1 : zero + one ≡ one
  pred (0+1≡1 i) = psuc zero

  1+0≡1 : one + zero ≡ one
  pred (1+0≡1 i) = psuc zero

∞ : Conat
pred ∞ = psuc ∞

∞+1≡∞ : succ ∞ ≡ ∞
pred (∞+1≡∞ _) = psuc ∞

succ∘pred≡id : ∀ n → unwrap-pred (pred (succ n)) ≡ n
succ∘pred≡id n _ = n

∞+2≡∞ : succ (succ ∞) ≡ ∞
∞+2≡∞ = compPath (cong succ ∞+1≡∞) ∞+1≡∞

∞+∞≡∞ : ∞ + ∞ ≡ ∞
pred (∞+∞≡∞ i) = psuc {!∞+1≡∞ ?!}

-- TODO: plus for conat, ∞ + ∞ ≡ ∞

