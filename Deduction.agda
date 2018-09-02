module Deduction where

open import Agda.Builtin.String

open import Formula
open import Ensemble
open import List
  hiding (Any ; any)
  renaming (
    All        to All[]        ;
    all        to all[]        ;
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    decide∈    to decide[∈]    )


infix 1 _⊢_
data _⊢_ : Ensemble formulaEq → Formula → Set where
  cite       : ∀{Γ α} → String → Γ ⊢ α → Γ ⊢ α
  assume     : (α : Formula)
               →                           α ∷ ∅ ⊢ α

  arrowintro : ∀{Γ β} → (α : Formula)
               →                             Γ ⊢ β
                                        ------------------- ⇒⁺ α
               →                         Γ - α ⊢ α ⇒ β

  arrowelim  : ∀{Γ₁ Γ₂ α β}
               →                 Γ₁ ⊢ α ⇒ β    →    Γ₂ ⊢ α
                                ----------------------------------- ⇒⁻
               →                         (Γ₁ ∪ Γ₂) ⊢ β

  conjintro  : ∀{Γ₁ Γ₂ α β}
               →                   Γ₁ ⊢ α    →    Γ₂ ⊢ β
                                  ------------------------------- ∧⁺
               →                       (Γ₁ ∪ Γ₂) ⊢ α ∧ β

  conjelim   : ∀{Γ₁ Γ₂ α β γ}
               →                 Γ₁ ⊢ α ∧ β    →    Γ₂ ⊢ γ
                                ----------------------------------- ∧⁻
               →                    Γ₁ ∪ ((Γ₂ - α) - β) ⊢ γ

  disjintro₁ : ∀{Γ α} → (β : Formula)
               →                             Γ ⊢ α
                                          --------------- ∨⁺₁
               →                           Γ ⊢ α ∨ β

  disjintro₂ : ∀{Γ β} → (α : Formula)
               →                             Γ ⊢ β
                                          --------------- ∨⁺₂
               →                           Γ ⊢ α ∨ β

  disjelim   : ∀{Γ₁ Γ₂ Γ₃ α β γ}
               →        Γ₁ ⊢ α ∨ β    →    Γ₂ ⊢ γ    →    Γ₃ ⊢ γ
                       ------------------------------------------------------ ∨⁻
               →                 (Γ₁ ∪ (Γ₂ - α)) ∪ (Γ₃ - β) ⊢ γ

  univintro  : ∀{Γ α} → (x : Variable)
               → All (varterm x BoundIn_) Γ
               →                             Γ ⊢ α
                                          --------------- ∀⁺
               →                           Γ ⊢ Λ x α

  univelim   : ∀{Γ α x} → (r : Term)
               →                           Γ ⊢ Λ x α
                                  ------------------------------- ∀⁻
               →                   Γ ⊢ α [ (varterm x) / r ]

  existintro : ∀{Γ α α[x/r]} → (r : Term) → (x : Variable)
               → (α [ varterm x / r ]≡ α[x/r])
               →                           Γ ⊢ α[x/r]
                                   ----------------------------- ∃⁺
               →                           Γ ⊢ V x α

  existelim  : ∀{Γ₁ Γ₂ α β x}
               → All (varterm x BoundIn_) (β ∷ (Γ₂ - α))
               →                 Γ₁ ⊢ V x α    →    Γ₂ ⊢ β
                                ----------------------------------- ∃⁻
               →                       Γ₁ ∪ (Γ₂ - α) ⊢ β

  close      : ∀{Γ Δ α} → Γ ⊂ Δ → Γ ⊢ α → Δ ⊢ α


⊢_ : Formula → Set
⊢_ α = ∅ ⊢ α


Derivable : Scheme → Set
Derivable S = ∀ αs → ⊢ (Scheme.inst S αs)


_⊃_ : List Scheme → Scheme → Set
(Ω ⊃ Φ) = All[] (Derivable) Ω → Derivable Φ

infixr 1 _⊃_
