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
                                (∅ ∪  ((α ∨ (α ⇒ atom (mkrel zero zero) []) ⇒ atom (mkrel zero zero) [])   ~   ((List.[ refl ] -∷ ∅) ∪ (α ~ (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅))))))
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


pattern xvar  = mkvar 0
pattern yvar  = mkvar 1
pattern zvar  = mkvar 2
pattern var n = mkvar (suc (suc (suc n)))

x = varterm xvar
y = varterm yvar
z = varterm zvar

∀x ∃x ∀x¬ ∃x¬ ¬∀x ¬∃x ¬∀x¬ ¬∃x¬ : Formula → Formula
∀x Φ = Λ xvar Φ
∃x Φ = V xvar Φ
∀x¬ Φ = ∀x (¬ Φ)
∃x¬ Φ = ∃x (¬ Φ)
¬∀x Φ = ¬(∀x Φ)
¬∃x Φ = ¬(∃x Φ)
¬∀x¬ Φ = ¬(∀x¬ Φ)
¬∃x¬ Φ = ¬(∃x¬ Φ)

∀y ∃y ∀y¬ ∃y¬ ¬∀y ¬∃y ¬∀y¬ ¬∃y¬ : Formula → Formula
∀y Φ = Λ yvar Φ
∃y Φ = V yvar Φ
∀y¬ Φ = ∀y (¬ Φ)
∃y¬ Φ = ∃y (¬ Φ)
¬∀y Φ = ¬(∀y Φ)
¬∃y Φ = ¬(∃y Φ)
¬∀y¬ Φ = ¬(∀y¬ Φ)
¬∃y¬ Φ = ¬(∃y¬ Φ)

dp gmp : Formula → Formula
dp  Φx = ∃x(Φx ⇒ ∀x Φx)
gmp Φx = ¬∀x Φx ⇒ ∃x (¬ Φx)

dp→gmp : (∀ α → ⊢ (dp α)) → ∀ α → ⊢ (gmp α)
dp→gmp ⊢dp α = close
                ((Λ (mkvar zero) α ⇒ atom (mkrel zero zero) []) ~  (∅ ∪   ((α ⇒ Λ (mkvar zero) α) ~ (α ~  (((α ∷ ((α ⇒ Λ (mkvar zero) α) ∷ List.[ refl ])) -∷ ∅) ∪   (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅)))))))
                (arrowintro (¬∀x α)
                 (existelim (V∣ (mkvar zero) (α ⇒ atom (mkrel zero zero) []) ∷  ((α ⇒ Λ (mkvar zero) α) ~   (α ~(((Λ∣ (mkvar zero) α ⇒ atom []) ∷ ∅) ∪ (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅))))))
                  (⊢dp α)
                  (existintro x xvar (ident (α ⇒ atom (mkrel zero zero) []) (varterm (mkvar zero)))
                   (arrowintro α
                    (arrowelim
                     (assume (¬∀x α))
                     (arrowelim
                      (assume (α ⇒ ∀x α))
                      (assume α)))))))
