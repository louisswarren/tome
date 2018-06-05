open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Formula
open import Deduction
--open import Texify
open import common
open import sugar

open import Deck
open import Decdeck Formula (_≈_ {formula})



pf⇒refl : (p : Formula) → [] , p ~ (p ∷ ∅) ⊢ (p ⇒ p)
pf⇒refl p = arrowintro p (assume p)


pf⇒order : (p q r : Formula) → [] , (p ⇒ q ⇒ r) ~ (q ~ (p ~ ((((p ⇒ q ⇒ r) ∷ ∅) ∪ (p ∷ ∅)) ∪ (q ∷ ∅)))) ⊢ (p ⇒ q ⇒ r) ⇒ (q ⇒ p ⇒ r)
pf⇒order p q r = arrowintro (p ⇒ q ⇒ r) (arrowintro q (arrowintro p (arrowelim (arrowelim (assume (p ⇒ q ⇒ r)) (assume p)) (assume q))))
