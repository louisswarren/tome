open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Decidable
open import Deduction
open import Formula
--open import Texify
open import common


open import List
open import Ensemble


pf⇒refl : (p : Formula) → [] , ∅ ⊢ (p ⇒ p)
pf⇒refl p = close (p ~ (Any.[ refl ] -∷ ∅)) (arrowintro p (assume p))


pf⇒order : (p q r : Formula) → [] , (p ⇒ q ⇒ r) ∷ ∅ ⊢ (q ⇒ p ⇒ r)
pf⇒order p q r = close
                  -- Agda filled this part automatically
                  (q ~ (p ~ ((
                   ([ refl , (λ ()) ] ∷ ∅)
                   ∪ (Any.[ refl ] -∷ ∅))
                   ∪ ((p ∷ Any.[ refl ]) -∷ ∅))))
                  --
                  (arrowintro q
                   (arrowintro p
                    (arrowelim
                     (arrowelim
                      (assume (p ⇒ q ⇒ r))
                      (assume p))
                     (assume q))))
--bound : (p : Formula) → (x : Variable) → common.isTrue (not (isfree x (Λ x p)))
--bound p x = ?
--
--
pf-repl : (p : Formula) → (x y : Variable) → (varterm y BoundIn p) → [] , Λ x p ∷ ∅ ⊢ Λ y (p [ varterm x / varterm y ])
pf-repl p x y y-not-free = univintro y
                            (Λ x y-not-free ∷ ∅) -- This must be supplied
                            (univelim (varterm y) (assume (Λ x p)))

pf-regen : (p : Formula) → (x : Variable) → [] , Λ x p ∷ ∅ ⊢ Λ x (p [ varterm x / varterm x ])
pf-regen p x = univintro x (Λ∣ x p ∷ ∅) (univelim (varterm x) (assume (Λ x p)))


EqPred : Relation
EqPred = mkrel 2 "Equals"
EqFormula : Term → Term → Formula
EqFormula s t = atom EqPred (s ∷ (t ∷ []))

pf-partialex : (t : Term) → (x : Variable) → [] , EqFormula t t ∷ ∅ ⊢ V x (EqFormula (varterm x) ?)
pf-partialex t x x≢t = existintroeq t x (atom EqPred ) (assume (EqFormula t t))

--pf-partialex : (s t : Term) → (x : Variable) → [] , EqFormula (sub varterm x for s inside varterm x) (sub varterm x for s inside t) ∷ ∅ ⊢ V x (EqFormula (varterm x) t)
--pf-partialex s t x = existintro s x (assume (EqFormula (sub varterm x for s inside varterm x) (sub varterm x for s inside t)))
--
--pf-partialex' : (s t : Term) → (x : Variable) → [] , EqFormula s t ∷ ∅ ⊢ V x (EqFormula (varterm x) t)
--pf-partialex' s t x = existintroeq s x φ (assume (EqFormula s t))
--                      where
--                        φ : EqFormula s t ≡ EqFormula (sub varterm x for s inside varterm x) (sub varterm x for s inside t)
--                        φ = {! refl  !}
