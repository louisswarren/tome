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

infixr 4 _++_

remove : {A : Set} → (A → A → Bool) → A → List A → List A
remove cmp y [] = []
remove cmp y (x ∷ xs) with cmp y x
...                   | false = x ∷ remove cmp y xs
...                   | true  = remove cmp y xs


infixr 6 _∖_
_∖_ : List Formula → Formula → List Formula
xs ∖ y = remove formulacmp y xs

postulate _isNotFreeIn_ : Variable → List Formula → Set

postulate _[_/_] : Formula → Term → Term → Formula

infix 1 _⊢_
data _⊢_ : List Formula → Formula → Set where
  assume     : (α : Formula)
               →                    [ α ] ⊢ α

  arrowintro : ∀{Γ β} → (α : Formula)
               →                      Γ ⊢ β
                                 --------------- ⇒⁺ α
               →                  Γ ∖ α ⊢ α ⇒ β

  arrowelim  : ∀{Γ₁ Γ₂ α β}
               →            Γ₁ ⊢ α ⇒ β    →    Γ₂ ⊢ α
                           --------------------------- ⇒⁻
               →                  (Γ₁ ++ Γ₂) ⊢ β

  conjintro  : ∀{Γ₁ Γ₂ α β}
               →            Γ₁ ⊢ α      →      Γ₂ ⊢ β
                           --------------------------- ∧⁺
               →                (Γ₁ ++ Γ₂) ⊢ α ∧ β

  conjelim₁  : ∀{Γ α β}
               →                    Γ ⊢ α ∧ β
                                   ----------- ∧⁻₁
               →                      Γ ⊢ α

  conjelim₂  : ∀{Γ α β}
               →                    Γ ⊢ α ∧ β
                                   ----------- ∧⁻₂
               →                      Γ ⊢ β

  disjintro₁ : ∀{Γ α} → (β : Formula)
               →                      Γ ⊢ α
                                   ----------- ∨⁺₁
               →                    Γ ⊢ α ∨ β

  disjintro₂ : ∀{Γ β} → (α : Formula)
               →                      Γ ⊢ β
                                   ----------- ∨⁺₂
               →                    Γ ⊢ α ∨ β

  disjelim   : ∀{Γ₁ Γ₂ Γ₃ α β γ}
               →     Γ₁ ⊢ α ∨ β    →    Γ₂ ⊢ γ    →    Γ₃ ⊢ γ
                    ------------------------------------------ ∨⁻
               →          Γ₁ ++ (Γ₂ ∖ α) ++ (Γ₃ ∖ β) ⊢ γ

  univintro  : ∀{Γ α} → (x : Variable) → {_ : x isNotFreeIn Γ}
               →                      Γ ⊢ α
                                   ----------- ∀⁺
               →                    Γ ⊢ V x α

  univelim   : ∀{Γ α x} → (r : Term)
               →                    Γ ⊢ V x α
                           --------------------------- ∀⁻
               →            Γ ⊢ α [ (varterm x) / r ]

  existintro : ∀{Γ α} → (r : Term) → (x : Variable)
               →                      Γ ⊢ α
                         ------------------------------- ∃⁺
               →          Γ ⊢ Λ x α [ r / (varterm x) ]

  existelim  : ∀{Γ₁ Γ₂ α β x } → {_ : x isNotFreeIn (β ∷ (Γ₂ ∖ α))}
               →            Γ₁ ⊢ Λ x α    →    Γ₂ ⊢ β
                           --------------------------- ∃⁻
               →                Γ₁ ++ (Γ₂ ∖ α) ⊢ β
