
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Formula
open import common


_∈_ = Membership (_≈_ {formula})

infix 1 _⊢_ _⊢_
data _⊢_ : List Formula → Formula → Set where
  assume     : (α : Formula)
               →                               [ α ] ⊢ α

  arrowintro : ∀{Δ Γ β} → (α : Formula) → {_ : (Δ ∖ α) ≡ Γ}
               →                                 Δ ⊢ β
                                        ------------------- ⇒⁺ α
               →                             Γ     ⊢ α ⇒ β

--             →                                 Γ ⊢ β
--                                      ------------------- ⇒⁺ α
--             →                             Γ ∖ α ⊢ α ⇒ β

  arrowelim  : ∀{Γ₁ Γ₂ α β}
               →                     Γ₁ ⊢ α ⇒ β    →        Γ₂ ⊢ α
                                ----------------------------------- ⇒⁻
               →                             (Γ₁ ++ Γ₂) ⊢ β

reorder : ∀ p q r → (p ⇒ (q ⇒ r)) ∷ [] ⊢ (q ⇒ (p ⇒ r))
reorder p q r = arrowintro q {{!   !}} (arrowintro p {?} (arrowelim (arrowelim (assume (p ⇒ r ⇒ r)) (assume p)) (assume r)))
