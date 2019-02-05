{-# OPTIONS --cubical --safe --guardedness #-}
module Cubical.Codata.Conat.Properties where

open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Core.Everything

open import Cubical.Codata.Conat.Base

open Conat

succ : Conat → Conat
prev (succ a) = inr a

Unwrap-prev : Prev -> Set
Unwrap-prev  zero   = Unit
Unwrap-prev (suc _) = Conat

unwrap-prev : (n : Prev) -> Unwrap-prev n
unwrap-prev  zero   = _
unwrap-prev (suc x) = x

private -- tests
  𝟘 = conat zero
  one  = succ 𝟘
  two  = succ one

  succOne≡two : succ one ≡ two
  succOne≡two i = two

  predTwo≡one : unwrap-prev (prev two) ≡ one
  predTwo≡one i = one

∞ : Conat
prev ∞ = suc ∞

∞+1≡∞ : succ ∞ ≡ ∞
prev (∞+1≡∞ _) = suc ∞

∞+2≡∞ : succ (succ ∞) ≡ ∞
∞+2≡∞ = compPath (cong succ ∞+1≡∞) ∞+1≡∞

-- TODO: plus for conat, ∞ + ∞ ≡ ∞

module Equality≅Bisimulation where

  open import Cubical.Data.Prod

  data _≠0 : (a : Prev) → Set where
    no0 : ∀ {a} → suc a ≠0

  pred : Prev → Conat
  prev (pred  zero  ) = zero
  prev (pred (suc x)) = prev x

  record _~_ (a b : Conat) : Set where
    coinductive
    constructor intro
    field proof : (a ≡ b) ⊎ ((pred (prev a) ~ pred (prev b)) × (prev a ≠0 × prev b ≠0))
  open _~_

  identity : ∀ n → n ~ n
  proof (identity n) with prev n
  ... | zero  = inl refl
  ... | suc x = inr (identity (pred (suc x)) , no0 , no0)

  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with≡_ : (y : A) → x ≡ y → Singleton x

  inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
  inspect x = x with≡ refl

  -- notZero : ∀ a → prev a ≠0 → a ≡ succ (pred (prev a))
  -- notZero a b with prev a
  -- notZero a ()  | zero
  -- notZero a no0 | suc x = cong {!!} (notZero {!x!} no0)

  {-# NON_TERMINATING #-}
  bisim : ∀ {a b} → a ~ b → a ≡ b
  bisim {a} {b} p with inspect (prev a) | inspect (prev b) | proof p
  ... | _ | _ | inl x = x
  ... | suc x with≡ xeq | suc y with≡ yeq | suc (bi , xn0 , yn0) = cong {!!} (bisim bi)
    -- a                    ≡⟨ notZero a xn0 ⟩
    -- succ (pred (prev a)) ≡⟨ (cong succ (bisim bi)) ⟩
    -- succ (pred (prev b)) ≡⟨ sym (notZero b yn0) ⟩
    -- b ∎

  misib : ∀ {a b} → a ≡ b → a ~ b
  proof (misib p) = inl p
