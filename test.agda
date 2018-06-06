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
open import Declist Formula (_≈_ {formula})

open import Search using (isTrue)

postulate ≈refl : {t : FormulaComponent} → (x : componentType t) → Search.isTrue (x ≈ x)


pf⇒refl : (p : Formula) → [] , p ~ (p ∷ ∅) ⊢ (p ⇒ p)
pf⇒refl p = arrowintro p (assume p)


pf⇒order : (p q r : Formula) → [] , (p ⇒ q ⇒ r) ~ (q ~ (p ~ ((((p ⇒ q ⇒ r) ∷ ∅) ∪ (p ∷ ∅)) ∪ (q ∷ ∅)))) ⊢ (p ⇒ q ⇒ r) ⇒ (q ⇒ p ⇒ r)
pf⇒order p q r = arrowintro (p ⇒ q ⇒ r) (arrowintro q (arrowintro p (arrowelim (arrowelim (assume (p ⇒ q ⇒ r)) (assume p)) (assume q))))

pf⇒order' : (p q r : Formula) → [] , ∅ ⊢ (p ⇒ q ⇒ r) ⇒ (q ⇒ p ⇒ r)
pf⇒order' p q r = proof (arrowintro (p ⇒ q ⇒ r) (arrowintro q (arrowintro p (arrowelim (arrowelim (assume (p ⇒ q ⇒ r)) (assume p)) (assume q)))))
                  (reduct~ (reduct~ (reduct~ (reduct∪ (reduct∪ (reduct∈∷ (tail (tail (head (≈refl (p ⇒ q ⇒ r))))) reduct∅) (reduct∈∷ (head (≈refl p)) reduct∅)) (reduct∈∷ (tail (head (≈refl q))) reduct∅)))))
