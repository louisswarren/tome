module Deduction where

open import Agda.Builtin.String

open import Formula
open import Ensemble
open import List renaming (All to All[])

private
  _NotFreeInAll_ : Variable → Ensemble formulaEq → Set
  x NotFreeInAll Γ = All (x NotFreeIn_) Γ


infix 1 _⊢_ ⊢_
data _⊢_ : Ensemble formulaEq → Formula → Set where
  cite        : ∀{α} → String → ∅ ⊢ α → ∅ ⊢ α

  close       : ∀{Γ Δ α} → Γ ⊂ Δ  → Γ ⊢ α → Δ ⊢ α

  univrename  : ∀{Γ α α[x/y] x y}
                → y NotFreeIn α → α [ x / varterm y ]≡ α[x/y]
                →                              Γ ⊢ Λ x α
                                            ----------------
                →                            Γ ⊢ Λ y α[x/y]

  existrename : ∀{Γ α α[x/y] x y}
                → y NotFreeIn α → α [ x / varterm y ]≡ α[x/y]
                →                              Γ ⊢ V x α
                                            ----------------
                →                            Γ ⊢ V y α[x/y]

  assume      : (α : Formula)
                →                              α ∷ ∅ ⊢ α

  arrowintro  : ∀{Γ β} → (α : Formula)
                →                                  Γ ⊢ β
                                              --------------- ⇒⁺ α
                →                              Γ - α ⊢ α ⇒ β

  arrowelim   : ∀{Γ₁ Γ₂ α β}
                →                          Γ₁ ⊢ α ⇒ β    →    Γ₂ ⊢ α
                                          --------------------------- ⇒⁻
                →                                 Γ₁ ∪ Γ₂ ⊢ β

  conjintro   : ∀{Γ₁ Γ₂ α β}
                →                           Γ₁ ⊢ α    →    Γ₂ ⊢ β
                                           ----------------------- ∧⁺
                →                              Γ₁ ∪ Γ₂ ⊢ α ∧ β

  conjelim    : ∀{Γ₁ Γ₂ α β γ}
                →                         Γ₁ ⊢ α ∧ β    →    Γ₂ ⊢ γ
                                         --------------------------- ∧⁻
                →                           Γ₁ ∪ (Γ₂ - α - β) ⊢ γ

  disjintro₁  : ∀{Γ α} → (β : Formula)
                →                                   Γ ⊢ α
                                                 ----------- ∨⁺₁
                →                                 Γ ⊢ α ∨ β

  disjintro₂  : ∀{Γ β} → (α : Formula)
                →                                   Γ ⊢ β
                                                 ----------- ∨⁺₂
                →                                 Γ ⊢ α ∨ β

  disjelim    : ∀{Γ₁ Γ₂ Γ₃ α β γ}
                →             Γ₁ ⊢ α ∨ β    →    Γ₂ ⊢ γ    →    Γ₃ ⊢ γ
                             ------------------------------------------ ∨⁻
                →                   Γ₁ ∪ (Γ₂ - α) ∪ (Γ₃ - β) ⊢ γ

  univintro   : ∀{Γ α} → (x : Variable)
                → x NotFreeInAll Γ
                →                                   Γ ⊢ α
                                                 ----------- ∀⁺
                →                                 Γ ⊢ Λ x α

  univelim    : ∀{Γ α x α[x/r]} → (r : Term)
                → α [ x / r ]≡ α[x/r]
                →                                Γ ⊢ Λ x α
                                                ------------ ∀⁻
                →                                Γ ⊢ α[x/r]

  existintro  : ∀{Γ α α[x/r]} → (r : Term) → (x : Variable)
                → α [ x / r ]≡ α[x/r]
                →                                Γ ⊢ α[x/r]
                                                ------------ ∃⁺
                →                                Γ ⊢ V x α

  existelim   : ∀{Γ₁ Γ₂ α β x}
                → x NotFreeInAll (β ∷ (Γ₂ - α))
                →                         Γ₁ ⊢ V x α    →    Γ₂ ⊢ β
                                         --------------------------- ∃⁻
                →                             Γ₁ ∪ (Γ₂ - α) ⊢ β

⊢_ : Formula → Set
⊢ α = ∅ ⊢ α


Derivable : Scheme → Set
Derivable S = ∀ αs → ⊢ (Scheme.inst S αs)

infix 1 _⊃_
_⊃_ : List Scheme → Scheme → Set
(Ω ⊃ Φ) = All[] (Derivable) Ω → Derivable Φ
