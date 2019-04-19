module Deductionraw where

open import Agda.Builtin.String

open import Formula
open import Ensemble

private
  _NotFreeInAll_ : Variable → Ensemble formulaEq → Set
  x NotFreeInAll Γ = All (x NotFreeIn_) Γ

infix 1 _⊢_ ⊢_
data _⊢_ : Ensemble formulaEq → Formula → Set where

  cite        : ∀{α} → String → ∅ ⊢ α → ∅ ⊢ α

  close       : ∀{Γ Δ α} → Γ ⊂ Δ  → Γ ⊢ α → Δ ⊢ α

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

postulate ≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α

open import Agda.Builtin.Equality
open import List
open import Decidable

rename : ∀{Γ α α′} → α ≈ α′ → Γ ⊢ α → Γ ⊢ α′
rename                                refl          Γ⊢α = Γ⊢α
rename {Γ} {α ⇒ β} {α′ ⇒ β′} (α/ ⇒ β/) Γ⊢α⇒β = close (lemma Γ α′) (arrowintro α′ (rename β/ (arrowelim Γ⊢α⇒β (rename (≈sym α/) (assume α′)))))
  where
    lemma : (Γ : Ensemble formulaEq) → (α : Formula) → ((Γ ∪ (α ∷ ∅)) - α) ⊂ Γ
    lemma ∅ α = α ~ ∅ ∪ List.Any.[ refl ] -∷ ∅
    lemma (β ∷ Γ) α with lemma Γ β
    lemma (β ∷ Γ) α | .β ~ c = {!   !}
    lemma (Γ - β) α = {!   !}
    lemma (Γ₁ ∪ Γ₂) α = {!   !}
rename {Γ} {α ∧ β} {α′ ∧ β′} (α/ ∧ β/) Γ⊢α∧β = close {!   !} (conjelim Γ⊢α∧β (conjintro (rename α/ (assume α)) (rename β/ (assume β))))
rename {Γ} {α ∨ β} {α′ ∨ β′} (α/ ∨ β/) Γ⊢α∨β = close {!   !} (disjelim Γ⊢α∨β (disjintro₁ β′ (rename α/ (assume α))) (disjintro₂ α′ (rename β/ (assume β))))
rename {Γ} {Λ x α} {Λ .x α′} (Λ a/)    Γ⊢Λxα = {!   !}
rename {Γ} {.(Λ _ _)}  {.(Λ _ _)}     (Λ/ β x x₁ e) Γ⊢α = {!   !}
rename {Γ} {.(V _ _)}  {.(V _ _)}     (V e)         Γ⊢α = {!   !}
rename {Γ} {.(V _ _)}  {.(V _ _)}     (V/ β x x₁ e) Γ⊢α = {!   !}

