module Deduction where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)

open import Agda.Builtin.Sigma using (fst ; snd)

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
               →                         Ω , (Γ₁ ∪ Γ₂) ⊢ β

  conjintro  : ∀{Γ₁ Γ₂ α β}
               →                   Ω , Γ₁ ⊢ α    →    Ω , Γ₂ ⊢ β
                                  ------------------------------- ∧⁺
               →                       Ω , (Γ₁ ∪ Γ₂) ⊢ α ∧ β

  conjelim   : ∀{Γ₁ Γ₂ α β γ}
               →                 Ω , Γ₁ ⊢ α ∧ β    →    Ω , Γ₂ ⊢ γ
                                ----------------------------------- ∧⁻
               →                    Ω , Γ₁ ∪ ((Γ₂ - α) - β) ⊢ γ

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

  univintro  : ∀{Γ α} → (x : Variable) → All (varterm x BoundIn_) Γ
               →                             Ω , Γ ⊢ α
                                          --------------- ∀⁺
               →                           Ω , Γ ⊢ Λ x α

  univelim   : ∀{Γ α x} → (r : Term)
               →                           Ω , Γ ⊢ Λ x α
                                  ------------------------------- ∀⁻
               →                   Ω , Γ ⊢ α [ (varterm x) / r ]

  existintro : ∀{Γ α} → (r : Term) → (x : Variable)
               →                    Ω , Γ ⊢ α [ varterm x / r ]
                                   ----------------------------- ∃⁺
               →                           Ω , Γ ⊢ V x α

  existelim  : ∀{Γ₁ Γ₂ α β x} → All (varterm x BoundIn_) (β ∷ (Γ₂ - α))
               →                 Ω , Γ₁ ⊢ V x α    →    Ω , Γ₂ ⊢ β
                                ----------------------------------- ∃⁻
               →                       Ω , Γ₁ ∪ (Γ₂ - α) ⊢ β

  close      : ∀{Γ Δ α} → Γ ⊂ Δ → Ω , Γ ⊢ α → Ω , Δ ⊢ α

existintroeq : ∀{α β Ω Γ} → (r : Term) → (x : Variable)
               → α [ varterm x / r ]≡ β
               →                             Ω , Γ ⊢ β
                                   ----------------------------- ∃⁺
               →                           Ω , Γ ⊢ V x α
existintroeq {α} {β} r x rep d with repWitness rep
existintroeq {α} {.(fst (α [ varterm x / r ]′))} r x rep d | refl = existintro r x d

_⊢_ : Ensemble formulaEq → Formula → Set
Γ ⊢ α = [] , Γ ⊢ α

_⊃_ : List Scheme → Scheme → Set
(Ω ⊃ Φ) = (xs : Vec Formula (Scheme.arity Φ)) → Ω , ∅ ⊢ Scheme.inst Φ xs

infixr 1 _⊃_

⊢ : Formula → Set
⊢ α = ∀{Ω} → Ω , ∅ ⊢ α

conclusion : ∀{Ω Γ α} → Ω , Γ ⊢ α → Formula
conclusion {_} {_} {α} _ = α

assumptions : ∀{Ω Γ α} → Ω , Γ ⊢ α → Ensemble formulaEq
assumptions {_} {Γ} {_} _ = Γ
