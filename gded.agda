
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Formula
open import common


_∈_ = Membership (_≈_ {formula})

infix 1 _⊢_ _⊢_
data _⊢_ : List Formula → Formula → Set where
  assume     : ∀{Γ₋ Γ₊} → (α : Formula)
               →                           Γ₋ ++ α ∷ Γ₊ ⊢ α

  -- Doesn't allow vacuous introduction
  arrowintro : ∀{Γ₋ Γ₊ β} → (α : Formula)
               →                           Γ₋ ++ α ∷ Γ₊ ⊢ β
                                        ------------------- ⇒⁺ α
               →                           Γ₋ ++ Γ₊ ⊢ α ⇒ β

  arrowelim  : ∀{Γ₁ Γ₂ α β}
               →                     Γ₁ ⊢ α ⇒ β    →        Γ₂ ⊢ α
                                ----------------------------------- ⇒⁻
               →                             (Γ₁ ++ Γ₂) ⊢ β

lemma : ∀ p q r → (p ⇒ q ⇒ r) ∷ p ∷ q ∷ [] ⊢ r → (p ⇒ q ⇒ r) ∷ [] ⊢ (q ⇒ (p ⇒ r))
lemma p q r d = arrowintro {p ⇒ q ⇒ r ∷ []} {[]} q (arrowintro {p ⇒ q ⇒ r ∷ []} {q ∷ []} p d)

reorder : ∀ p q r → (p ⇒ (q ⇒ r)) ∷ [] ⊢ (q ⇒ (p ⇒ r))
---reorder p q r = lemma p q r (arrowelim (arrowelim (assume {[]} {[]} (p ⇒ q ⇒ r)) (assume {[]} {[]} p)) (assume {[]} {[]} q))
reorder p q r = arrowintro {p ⇒ q ⇒ r ∷ []} {[]} q
                 (arrowintro {p ⇒ q ⇒ r ∷ []} {q ∷ []} p
                  (arrowelim
                   (arrowelim
                    (assume {[]} {[]} (p ⇒ q ⇒ r))
                    (assume {[]} {[]} p))
                   (assume {[]} {[]} q)))
