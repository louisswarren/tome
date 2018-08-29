module Deduction where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)

open import Agda.Builtin.Sigma using (fst ; snd)
open import Agda.Builtin.String

open import Formula
open import Deck
open import Ensemble
open import List
  hiding (Any ; any)
  renaming (
    All        to All[]        ;
    all        to all[]        ;
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    decide∈    to decide[∈]    )
open import common

record Scheme : Set where
  constructor scheme
  field
    idx   : String
    arity : ℕ
    inst  : Vec Formula arity → Formula

infix 1 _⊢_
data _⊢_ : Ensemble formulaEq → Formula → Set where
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

  univintro  : ∀{Γ α} → (x : Variable) → All (varterm x BoundIn_) Γ
               →                             Γ ⊢ α
                                          --------------- ∀⁺
               →                           Γ ⊢ Λ x α

  univelim   : ∀{Γ α x} → (r : Term)
               →                           Γ ⊢ Λ x α
                                  ------------------------------- ∀⁻
               →                   Γ ⊢ α [ (varterm x) / r ]

  existintro : ∀{Γ α} → (r : Term) → (x : Variable)
               →                    Γ ⊢ α [ varterm x / r ]
                                   ----------------------------- ∃⁺
               →                           Γ ⊢ V x α

  existelim  : ∀{Γ₁ Γ₂ α β x} → All (varterm x BoundIn_) (β ∷ (Γ₂ - α))
               →                 Γ₁ ⊢ V x α    →    Γ₂ ⊢ β
                                ----------------------------------- ∃⁻
               →                       Γ₁ ∪ (Γ₂ - α) ⊢ β

  close      : ∀{Γ Δ α} → Γ ⊂ Δ → Γ ⊢ α → Δ ⊢ α

existintroeq : ∀{α β Γ} → (r : Term) → (x : Variable)
               → α [ varterm x / r ]≡ β
               →                             Γ ⊢ β
                                   ----------------------------- ∃⁺
               →                           Γ ⊢ V x α
existintroeq {α} {β} r x rep d with repWitness rep
existintroeq {α} {.(fst (α [ varterm x / r ]′))} r x rep d | refl = existintro r x d



⊢_ : Formula → Set
⊢_ α = ∅ ⊢ α

Derivable : Scheme → Set
Derivable S = ∀ αs → ⊢ (Scheme.inst S αs)

_⊃_ : List Scheme → Scheme → Set
(Ω ⊃ Φ) = All[] (Derivable) Ω → Derivable Φ

infixr 1 _⊃_


⊥ : Formula
⊥ = atom (mkprop 0) []

¬ ¬¬ : Formula → Formula
¬ α = α ⇒ ⊥
¬¬ α = ¬ (¬ α)

dne : Vec Formula 1 → Formula
dne (x ∷ []) = ¬¬ x ⇒ x

lem : Vec Formula 1 → Formula
lem (x ∷ []) = x ∨ ¬ x

DNE : Scheme
DNE = scheme "DNE" 1 dne

LEM : Scheme
LEM = scheme "LEM" 1 lem

dne→lem : (∀ αs → ⊢ (dne αs)) → ∀ αs → ⊢ (lem αs)
dne→lem ⊢dne (α ∷ []) = close
                                (∅ ∪  ((α ∨ (α ⇒ atom (mkrel zero zero) []) ⇒ atom (mkrel zero zero) [])   ~   ((List.[ refl ] -∷ ∅) ∪;(α ~ (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅))))))
                                (arrowelim
                                 (⊢dne ((α ∨ ¬ α) ∷ []))
                                 (arrowintro (¬ (α ∨ ¬ α))
                                  (arrowelim
                                   (assume (¬ (α ∨ ¬ α)))
                                   (disjintro₂ α
                                    (arrowintro α
                                     (arrowelim
                                      (assume (¬ (α ∨ ¬ α)))
                                      (disjintro₁ (¬ α)
                                       (assume α))))))))

DNE⊃LEM : DNE ∷ [] ⊃ LEM
DNE⊃LEM (⊢dne ∷ []) (α ∷ []) = dne→lem ⊢dne (α ∷ [])
