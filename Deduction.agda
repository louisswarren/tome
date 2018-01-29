module Deduction where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Formula
open import common

data _,_⊢_ : List Formula → List Formula → Formula → Set

_⊢_ : List Formula → Formula → Set
Γ ⊢ α = [] , Γ ⊢ α

_∈_ = membership formulacmp

infix 1 _⊢_ _,_⊢_
data _,_⊢_ where
  axiom      : ∀{Ω} → (α : Formula) → {_ : α ∈ Ω}
               →                             Ω , [] ⊢ α

  assume     : ∀{Ω} → (α : Formula)
               →                           Ω , [ α ] ⊢ α

  arrowintro : ∀{Ω Γ β} → (α : Formula)
               →                             Ω , Γ ⊢ β
                                        ------------------- ⇒⁺ α
               →                         Ω , Γ ∖ α ⊢ α ⇒ β

  arrowelim  : ∀{Ω Γ₁ Γ₂ α β}
               →                 Ω , Γ₁ ⊢ α ⇒ β    →    Ω , Γ₂ ⊢ α
                                ----------------------------------- ⇒⁻
               →                         Ω , (Γ₁ ++ Γ₂) ⊢ β

  conjintro  : ∀{Ω Γ₁ Γ₂ α β}
               →                   Ω , Γ₁ ⊢ α    →    Ω , Γ₂ ⊢ β
                                  ------------------------------- ∧⁺
               →                       Ω , (Γ₁ ++ Γ₂) ⊢ α ∧ β

  conjelim   : ∀{Ω Γ₁ Γ₂ α β γ}
               →                 Ω , Γ₁ ⊢ α ∧ β    →    Ω , Γ₂ ⊢ γ
                                ----------------------------------- ∧⁻
               →                     Ω , Γ₁ ++ (Γ₂ ∖ α ∖ β) ⊢ γ

  disjintro₁ : ∀{Ω Γ α} → (β : Formula)
               →                             Ω , Γ ⊢ α
                                          --------------- ∨⁺₁
               →                           Ω , Γ ⊢ α ∨ β

  disjintro₂ : ∀{Ω Γ β} → (α : Formula)
               →                             Ω , Γ ⊢ β
                                          --------------- ∨⁺₂
               →                           Ω , Γ ⊢ α ∨ β

  disjelim   : ∀{Ω Γ₁ Γ₂ Γ₃ α β γ}
               →        Ω , Γ₁ ⊢ α ∨ β    →    Ω , Γ₂ ⊢ γ    →    Ω , Γ₃ ⊢ γ
                       ------------------------------------------------------ ∨⁻
               →                 Ω , Γ₁ ++ (Γ₂ ∖ α) ++ (Γ₃ ∖ β) ⊢ γ

  univintro  : ∀{Ω Γ α} → (x : Variable) → {_ : x isNotFreeIn Γ}
               →                             Ω , Γ ⊢ α
                                          --------------- ∀⁺
               →                           Ω , Γ ⊢ Λ x α

  univelim   : ∀{Ω Γ α x} → (r : Term)
               →                           Ω , Γ ⊢ Λ x α
                                  ------------------------------- ∀⁻
               →                   Ω , Γ ⊢ α [ (varterm x) / r ]

  existintro : ∀{Ω Γ α} → (r : Term) → (x : Variable)
               →                             Ω , Γ ⊢ α
                                ----------------------------------- ∃⁺
               →                 Ω , Γ ⊢ V x α [ r / (varterm x) ]

  existelim  : ∀{Ω Γ₁ Γ₂ α β x } → {_ : x isNotFreeIn (β ∷ (Γ₂ ∖ α))}
               →                 Ω , Γ₁ ⊢ V x α    →    Ω , Γ₂ ⊢ β
                                ----------------------------------- ∃⁻
               →                       Ω , Γ₁ ++ (Γ₂ ∖ α) ⊢ β

_⊃_ : List Formula → Formula → Set
Ω ⊃ Φ = Ω , [] ⊢ Φ
