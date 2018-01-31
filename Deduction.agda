module Deduction where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Formula
open import Scheme
open import common

data _,_⊢_ : ∀{m} → Vec ΣScheme m → List Formula → Formula → Set

_⊢_ : List Formula → Formula → Set
Γ ⊢ α = [] , Γ ⊢ α

_∈_ = Membership formulacmp

infix 1 _⊢_ _,_⊢_
data _,_⊢_ where
  axiom      : ∀{n} → {Ω : Vec ΣScheme n} → (k : ℕ)
               → {indexable : isTrue (k < n)}
               → (x : Vec Formula (Σ.fst ((Ω ! k) {indexable})))
               → Ω , [] ⊢ (_-aryScheme.func (Σ.snd (Ω ! k))) x

  assume     : ∀{n} → {Ω : Vec ΣScheme n} → (α : Formula)
               →                           Ω , [ α ] ⊢ α

  arrowintro : ∀{n Γ β} → {Ω : Vec ΣScheme n} → (α : Formula)
               →                             Ω , Γ ⊢ β
                                        ------------------- ⇒⁺ α
               →                         Ω , Γ ∖ α ⊢ α ⇒ β

  arrowelim  : ∀{n Γ₁ Γ₂ α β} → {Ω : Vec ΣScheme n}
               →                 Ω , Γ₁ ⊢ α ⇒ β    →    Ω , Γ₂ ⊢ α
                                ----------------------------------- ⇒⁻
               →                         Ω , (Γ₁ ++ Γ₂) ⊢ β

  conjintro  : ∀{n Γ₁ Γ₂ α β} → {Ω : Vec ΣScheme n}
               →                   Ω , Γ₁ ⊢ α    →    Ω , Γ₂ ⊢ β
                                  ------------------------------- ∧⁺
               →                       Ω , (Γ₁ ++ Γ₂) ⊢ α ∧ β

  conjelim   : ∀{n Γ₁ Γ₂ α β γ} → {Ω : Vec ΣScheme n}
               →                 Ω , Γ₁ ⊢ α ∧ β    →    Ω , Γ₂ ⊢ γ
                                ----------------------------------- ∧⁻
               →                     Ω , Γ₁ ++ (Γ₂ ∖ α ∖ β) ⊢ γ

  disjintro₁ : ∀{n Γ α} → {Ω : Vec ΣScheme n} → (β : Formula)
               →                             Ω , Γ ⊢ α
                                          --------------- ∨⁺₁
               →                           Ω , Γ ⊢ α ∨ β

  disjintro₂ : ∀{n Γ β} → {Ω : Vec ΣScheme n} → (α : Formula)
               →                             Ω , Γ ⊢ β
                                          --------------- ∨⁺₂
               →                           Ω , Γ ⊢ α ∨ β

  disjelim   : ∀{n Γ₁ Γ₂ Γ₃ α β γ} → {Ω : Vec ΣScheme n}
               →        Ω , Γ₁ ⊢ α ∨ β    →    Ω , Γ₂ ⊢ γ    →    Ω , Γ₃ ⊢ γ
                       ------------------------------------------------------ ∨⁻
               →                 Ω , Γ₁ ++ (Γ₂ ∖ α) ++ (Γ₃ ∖ β) ⊢ γ

  univintro  : ∀{n Γ α} → {Ω : Vec ΣScheme n} → (x : Variable) → {_ : x isNotFreeIn Γ}
               →                             Ω , Γ ⊢ α
                                          --------------- ∀⁺
               →                           Ω , Γ ⊢ Λ x α

  univelim   : ∀{n Γ α x} → {Ω : Vec ΣScheme n} → (r : Term)
               →                           Ω , Γ ⊢ Λ x α
                                  ------------------------------- ∀⁻
               →                   Ω , Γ ⊢ α [ (varterm x) / r ]

  existintro : ∀{n Γ α} → {Ω : Vec ΣScheme n} → (r : Term) → (x : Variable)
               →                             Ω , Γ ⊢ α
                                ----------------------------------- ∃⁺
               →                 Ω , Γ ⊢ V x α [ r / (varterm x) ]

  existelim  : ∀{n Γ₁ Γ₂ α β x } → {Ω : Vec ΣScheme n} → {_ : x isNotFreeIn (β ∷ (Γ₂ ∖ α))}
               →                 Ω , Γ₁ ⊢ V x α    →    Ω , Γ₂ ⊢ β
                                ----------------------------------- ∃⁻
               →                       Ω , Γ₁ ++ (Γ₂ ∖ α) ⊢ β

_⊃_ : ∀{n} → Vec ΣScheme n → Formula → Set
Ω ⊃ Φ = Ω , [] ⊢ Φ

conclusion : ∀{n Γ α} {Ω : Vec ΣScheme n} → Ω , Γ ⊢ α → Formula
conclusion {_} {_} {α} _ = α

assumptions : ∀{n Γ α} {Ω : Vec ΣScheme n} → Ω , Γ ⊢ α → List Formula
assumptions {_} {Γ} {_} _ = Γ

isclosed : ∀{Γ α n} {Ω : Vec ΣScheme n} → Formula → Ω , Γ ⊢ α → Bool
isclosed {Γ} α d = membership formulacmp α Γ
