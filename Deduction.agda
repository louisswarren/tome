module Deduction where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Formula

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

remove : {A : Set} → (A → A → Bool) → A → List A → List A
remove cmp y [] = []
remove cmp y (x ∷ xs) with cmp y x
...                   | false = x ∷ remove cmp y xs
...                   | true  = remove cmp y xs


infixr 6 _∖_
_∖_ : List Formula → Formula → List Formula
xs ∖ y = remove formulacmp y xs

infix 1 _⊢_
data _⊢_ : List Formula → Formula → Set where
  assume     : (α : Formula)          →                     [ α ] ⊢ α

  arrowintro : ∀{Γ β} → (α : Formula) →                       Γ ⊢ β
                                                         --------------- ⇒+ α
                                      →                   Γ ∖ α ⊢ α ⇒ β

  arrowelim  : ∀{Γ₁ Γ₂ α β}           →           Γ₁ ⊢ α ⇒ β    →    Γ₂ ⊢ α
                                                 --------------------------- ⇒-
                                      →                 (Γ₁ ++ Γ₂) ⊢ β

