module Deduction where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Formula
open import common

data _,_⊢_ : List Scheme → List Formula → Formula → Set

_⊢_ : List Formula → Formula → Set
Γ ⊢ α = [] , Γ ⊢ α

_∈_ = Membership formulacmp

infix 1 _⊢_ _,_⊢_
data _,_⊢_ where
  lemma      : ∀{Ω Γ α} → Ω , Γ ⊢ α → Ω , Γ ⊢ α

  axiom      : ∀{Ω} → (k : ℕ) → {indexable : isTrue (k < (len Ω))}
               → (x : Vec Formula (Scheme.arity ((Ω ! k) {indexable})))
               →                  Ω , [] ⊢ (Scheme.func (Ω ! k)) x

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

  univintro  : ∀{Ω Γ α} → (x : Variable)
               → {_ : x isNotFreeIn Γ}
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

  existelim  : ∀{Ω Γ₁ Γ₂ α β x} → {_ : x isNotFreeIn (β ∷ (Γ₂ ∖ α))}
               →                 Ω , Γ₁ ⊢ V x α    →    Ω , Γ₂ ⊢ β
                                ----------------------------------- ∃⁻
               →                       Ω , Γ₁ ++ (Γ₂ ∖ α) ⊢ β

_⊃_ : List Scheme → (s : Scheme) → Vec Formula (Scheme.arity s)  → Set
(Ω ⊃ Φ) xs = Ω , [] ⊢ Scheme.func Φ xs

infixr 1 _⊃_

⊢ : Formula → Set
⊢ α = ∀{Ω} → Ω , [] ⊢ α

conclusion : ∀{Ω Γ α} → Ω , Γ ⊢ α → Formula
conclusion {_} {_} {α} _ = α

assumptions : ∀{Ω Γ α} → Ω , Γ ⊢ α → List Formula
assumptions {_} {Γ} {_} _ = Γ

isclosed : ∀{Ω Γ α} → Formula → Ω , Γ ⊢ α → Bool
isclosed {_} {Γ} α d = membership formulacmp α Γ

open import Agda.Builtin.String

conc : ∀{a b c} → (a ⊃ b) c → String
conc {a} {b} d = Scheme.name b
