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


Q = atom (mkprop "Q") []
P : Term → Formula
P t = atom (mkrel 1 "P") (t ∷ [])

Px = P x
Py = P y
--------------------------------------------------------------------------------

lemf : Vec Formula 1 → Formula
lemf (α ∷ []) = α ∨ ¬ α
lem : Scheme
lem = scheme 1 "LEM" lemf

dgpf : Vec Formula 2 → Formula
dgpf (α ∷ β ∷ []) = (α ⇒ β) ∨ (β ⇒ α)
dgp : Scheme
dgp = scheme 2 "DGP" dgpf

dpf : Vec Formula 1 → Formula
dpf (α ∷ []) = ∃y ((α [ x / y ]) ⇒ (∀x α))
dp : Scheme
dp = scheme 1 "DP" dpf

gmpf : Vec Formula 1 → Formula
gmpf (α ∷ []) = ¬ (∀x α) ⇒ ∃x (¬ α)
gmp : Scheme
gmp = scheme 1 "GMP" gmpf


pf : dgp ∷ lem ∷ [] , ∅ ⊢ Q ∨ ¬ Q
pf = axiom 1 (Q ∷ [])


p-is-p : (p : Formula) → [] , p ~ (p ∷ ∅) ⊢ (p ⇒ p)
p-is-p p = arrowintro p (assume p)

--pf2 : dp ∷ [] , ∅ ⊢ gmpf (P x ∷ [])
--pf2 = arrowintro (¬∀x Px)
--          (existelim
--           (axiom 0 (Px ∷ []))
--           (existintro y xvar (arrowintro Py
--            (arrowelim (assume (¬∀x Px))
--             (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))))
--           )
--
----s = texify pf2
--
--
--
--
---- Let's do that again, but not assume that x is the free variable
--
--dpsf : Variable → Vec Formula 1 → Formula
--dpsf v (α ∷ []) = ∃y ((α [ varterm v / y ]) ⇒ (∀x (α [ varterm v / x ])))
--dps : Variable → Scheme
--dps v = scheme 1 "DP" (dpsf v)
--
--gmpsf : Variable → Vec Formula 1 → Formula
--gmpsf v (α ∷ []) = ¬ (∀x (α [ varterm v / x ])) ⇒ ∃x (¬ (α [ varterm v / x ]))
--gmps : Variable → Scheme
--gmps v = scheme 1 "GMP" (gmpsf v)
--
--
----pf3 : (dps xvar) ∷ [] , ∅ ⊢ gmpsf xvar (P x ∷ [])
----pf3 = arrowintro (¬∀x Px)
----          (existelim
----           (axiom 0 (Px ∷ []))
----           (existintro y xvar (arrowintro Py
----            (arrowelim (assume (¬∀x Px))
----             (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))))
----           )
