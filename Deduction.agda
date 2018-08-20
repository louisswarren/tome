module Deduction where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)

open import Formula
open import Deck
open import Ensemble
open import common


infix 1 _⊢_ _,_⊢_
data _,_⊢_ (Ω : List Scheme) : Ensemble formulaEq → Formula → Set where
  axiom      : (k : ℕ) → {indexable : isTrue (k < (len Ω))}
               → (x : Vec Formula (Scheme.arity ((Ω ! k) {indexable})))
               →                  Ω , ∅  ⊢ (Scheme.inst (Ω ! k)) x

  assume     : (α : Formula)
               →                           Ω , α ∷ ∅ ⊢ α

  arrowintro : ∀{Γ β} → (α : Formula)
               →                             Ω , Γ ⊢ β
                                        ------------------- ⇒⁺ α
               →                         Ω , Γ - α ⊢ α ⇒ β

  arrowelim  : ∀{Γ₁ Γ₂ α β}
               →                 Ω , Γ₁ ⊢ α ⇒ β    →    Ω , Γ₂ ⊢ α
                                ----------------------------------- ⇒⁻
               →                         Ω , (Γ₁ ∪  Γ₂) ⊢ β

  conjintro  : ∀{Γ₁ Γ₂ α β}
               →                   Ω , Γ₁ ⊢ α    →    Ω , Γ₂ ⊢ β
                                  ------------------------------- ∧⁺
               →                       Ω , (Γ₁ ∪  Γ₂) ⊢ α ∧ β

  conjelim   : ∀{Γ₁ Γ₂ α β γ}
               →                 Ω , Γ₁ ⊢ α ∧ β    →    Ω , Γ₂ ⊢ γ
                                ----------------------------------- ∧⁻
               →                    Ω , Γ₁ ∪  ((Γ₂ - α) - β) ⊢ γ

  disjintro₁ : ∀{Γ α} → (β : Formula)
               →                             Ω , Γ ⊢ α
                                          --------------- ∨⁺₁
               →                           Ω , Γ ⊢ α ∨ β

  disjintro₂ : ∀{Γ β} → (α : Formula)
               →                             Ω , Γ ⊢ β
                                          --------------- ∨⁺₂
               →                           Ω , Γ ⊢ α ∨ β

  disjelim   : ∀{Γ₁ Γ₂ Γ₃ α β γ}
               →        Ω , Γ₁ ⊢ α ∨ β    →    Ω , Γ₂ ⊢ γ    →    Ω , Γ₃ ⊢ γ
                       ------------------------------------------------------ ∨⁻
               →                 Ω , (Γ₁ ∪ (Γ₂ - α)) ∪ (Γ₃ - β) ⊢ γ

  univintro  : ∀{Γ α} → (x : Variable)
               → {_ : All (varterm x BoundIn_) Γ}
               →                             Ω , Γ ⊢ α
                                          --------------- ∀⁺
               →                           Ω , Γ ⊢ Λ x α

  univelim   : ∀{Γ α x} → (r : Term)
               →                           Ω , Γ ⊢ Λ x α
                                  ------------------------------- ∀⁻
               →                   Ω , Γ ⊢ α [ (varterm x) / r ]

  existintro : ∀{Γ α} → (r : Term) → (x : Variable)
               →                             Ω , Γ ⊢ α
                                ----------------------------------- ∃⁺
               →                 Ω , Γ ⊢ V x α [ r / (varterm x) ]

  existelim  : ∀{Γ₁ Γ₂ α β x} → {_ : All (varterm x BoundIn_) (β ∷ (Γ₂ - α))}
               →                 Ω , Γ₁ ⊢ V x α    →    Ω , Γ₂ ⊢ β
                                ----------------------------------- ∃⁻
               →                       Ω , Γ₁ ∪ (Γ₂ - α) ⊢ β

_⊢_ : Ensemble formulaEq → Formula → Set
Γ ⊢ α = [] , Γ ⊢ α

_⊃_ : List Scheme → (s : Scheme) → Vec Formula (Scheme.arity s)  → Set
(Ω ⊃ Φ) xs = Ω , ∅ ⊢ Scheme.inst Φ xs

infixr 1 _⊃_

⊢ : Formula → Set
⊢ α = ∀{Ω} → Ω , ∅ ⊢ α

conclusion : ∀{Ω Γ α} → Ω , Γ ⊢ α → Formula
conclusion {_} {_} {α} _ = α

assumptions : ∀{Ω Γ α} → Ω , Γ ⊢ α → Ensemble formulaEq
assumptions {_} {Γ} {_} _ = Γ

--isclosed : ∀{Ω Γ α} → Formula → Ω , Γ ⊢ α → Bool
--isclosed {_} {Γ} α d = membership _≈_ α Γ

open import Agda.Builtin.String

conc : ∀{a b c} → (a ⊃ b) c → String
conc {a} {b} d = Scheme.name b
