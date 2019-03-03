module Deduction where

open import Agda.Builtin.String

open import Formula
open import List
open import Decidable

private
  infix 300 _NotFreeInAll_
  _NotFreeInAll_ : Variable → List Formula → Set
  x NotFreeInAll Γ = All (x NotFreeIn_) Γ

_⊂_ : (αs βs : List Formula) → Set
αs ⊂ βs = All (_∈ βs) αs

infixl 4 _-_
_-_ : List Formula → Formula → List Formula
[] - β = []
(α ∷ αs) - β with formulaEq α β
((β ∷ αs) - .β) | yes refl = αs - β
((α ∷ αs) -  β) | no  _    = α ∷ (αs - β)

infixl 6 _∪_
_∪_ : List Formula → List Formula → List Formula
[]       ∪ ys = ys
(x ∷ xs) ∪ ys = x ∷ (xs ∪ ys)

infix 1 _⊢_ ⊢_
data _⊢_ : List Formula → Formula → Set where
  cite       : ∀{α} → String → [] ⊢ α → [] ⊢ α

  close      : ∀{Γ Δ α} → Γ ⊂ Δ  → Γ ⊢ α → Δ ⊢ α

  assume     : (α : Formula)
               →                              α ∷ [] ⊢ α

  arrowintro : ∀{Γ β} → (α : Formula)
               →                                  Γ ⊢ β
                                             --------------- ⇒⁺ α
               →                              Γ - α ⊢ α ⇒ β

  arrowelim  : ∀{Γ₁ Γ₂ α β}
               →                      Γ₁ ⊢ α ⇒ β    →    Γ₂ ⊢ α
                                     --------------------------- ⇒⁻
               →                            (Γ₁ ∪ Γ₂) ⊢ β

  conjintro  : ∀{Γ₁ Γ₂ α β}
               →                          Γ₁ ⊢ α    →    Γ₂ ⊢ β
                                         ----------------------- ∧⁺
               →                            (Γ₁ ∪ Γ₂) ⊢ α ∧ β

  conjelim   : ∀{Γ₁ Γ₂ α β γ}
               →                      Γ₁ ⊢ α ∧ β    →    Γ₂ ⊢ γ
                                     --------------------------- ∧⁻
               →                       Γ₁ ∪ ((Γ₂ - α) - β) ⊢ γ

  disjintro₁ : ∀{Γ α} → (β : Formula)
               →                                  Γ ⊢ α
                                               ----------- ∨⁺₁
               →                                Γ ⊢ α ∨ β

  disjintro₂ : ∀{Γ β} → (α : Formula)
               →                                  Γ ⊢ β
                                               ----------- ∨⁺₂
               →                                Γ ⊢ α ∨ β

  disjelim   : ∀{Γ₁ Γ₂ Γ₃ α β γ}
               →              Γ₁ ⊢ α ∨ β    →    Γ₂ ⊢ γ    →    Γ₃ ⊢ γ
                             ------------------------------------------ ∨⁻
               →                   (Γ₁ ∪ (Γ₂ - α)) ∪ (Γ₃ - β) ⊢ γ

  univintro  : ∀{Γ α} → (x : Variable)
               → x NotFreeInAll Γ
               →                                  Γ ⊢ α
                                               ----------- ∀⁺
               →                                Γ ⊢ Λ x α

  univelim   : ∀{Γ α x α[x/r]} → (r : Term)
               → α [ x / r ]≡ α[x/r]
               →                                  Γ ⊢ Λ x α
                                                 ------------ ∀⁻
               →                                  Γ ⊢ α[x/r]

  existintro : ∀{Γ α α[x/r]} → (r : Term) → (x : Variable)
               → α [ x / r ]≡ α[x/r]
               →                                  Γ ⊢ α[x/r]
                                                 ------------ ∃⁺
               →                                  Γ ⊢ V x α

  existelim  : ∀{Γ₁ Γ₂ α β x}
               → x NotFreeInAll (β ∷ (Γ₂ - α))
               →                      Γ₁ ⊢ V x α    →    Γ₂ ⊢ β
                                     --------------------------- ∃⁻
               →                          Γ₁ ∪ (Γ₂ - α) ⊢ β


⊢_ : Formula → Set
⊢_ α = [] ⊢ α


Derivable : Scheme → Set
Derivable S = ∀ αs → ⊢ (Scheme.inst S αs)


_⊃_ : List Scheme → Scheme → Set
(Ω ⊃ Φ) = All (Derivable) Ω → Derivable Φ

infixr 1 _⊃_


eqded : ∀{α Δ Γ}→ Δ ≡ Γ → Δ ⊢ α → Γ ⊢ α
eqded refl x₁ = x₁



simple : ∀ α → [] ⊢ α ⇒ α
simple α = eqded closed
           (arrowintro α
            (assume α))
  where
    closed : ((α ∷ []) - α) ≡ []
    closed with formulaEq α α
    closed | yes refl = refl
    closed | no x = ⊥-elim (x refl)

removeonce : ∀ α → (α ∷ α ∷ [] - α) ≡ []
removeonce α with formulaEq α α
removeonce α | yes refl with formulaEq α α
removeonce α | yes refl | yes refl = refl
removeonce α | yes refl | no x = ⊥-elim (x refl)
removeonce α | no x = ⊥-elim (x refl)

simple₂ : ∀ α β → [] ⊢ α ⇒ α ∧ (β ⇒ α)
simple₂ α β = eqded closed (arrowintro α (conjintro (assume α) (arrowintro β (assume α))))
  where
    closed : (((α ∷ []) ∪ ((α ∷ []) - β)) - α) ≡ []
    closed with formulaEq α β
    closed | yes refl with formulaEq α α
    closed | yes refl | yes refl = refl
    closed | yes refl | no x = ⊥-elim (x refl)
    closed | no _ with formulaEq α α
    closed | no _ | yes refl with formulaEq α α
    closed | no _ | yes refl | yes refl = refl
    closed | no _ | yes refl | no x = ⊥-elim (x refl)
    closed | no _ | no x = ⊥-elim (x refl)

reorder : ∀ α β γ → α ⇒ β ⇒ γ ∷ [] ⊢ β ⇒ α ⇒ γ
reorder α β γ = eqded closed
                (arrowintro β
                 (arrowintro α
                  (arrowelim
                   (arrowelim
                    (assume (α ⇒ β ⇒ γ))
                    (assume α))
                   (assume β))))
  where
    closed : ((α ⇒ β ⇒ γ ∷ α ∷ β ∷ []) - α - β) ≡ α ⇒ β ⇒ γ ∷ []
    closed with formulaEq (α ⇒ β ⇒ γ) α
    closed | yes ()
    closed | no _ with formulaEq α α
    closed | no _ | no x     = ⊥-elim (x refl)
    closed | no _ | yes refl with formulaEq β α
    closed | no _ | yes refl | yes refl with formulaEq (α ⇒ β ⇒ γ) β
    closed | no _ | yes refl | yes refl | yes ()
    closed | no _ | yes refl | yes refl | no _ = refl
    closed | no _ | yes refl | no _ with formulaEq (α ⇒ β ⇒ γ) β
    closed | no _ | yes refl | no _ | yes ()
    closed | no _ | yes refl | no _ | no _ with formulaEq β β
    closed | no _ | yes refl | no _ | no _ | yes refl = refl
    closed | no _ | yes refl | no _ | no _ | no x = ⊥-elim (x refl)
