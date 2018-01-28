open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Formula
open import Deduction
open import common

Q = propatom (mkprop "Q")

xvar yvar : Variable
xvar = mkvar "x"
yvar = mkvar "y"

x = varterm xvar
y = varterm yvar

_-aryPred : (n : ℕ) → Set
(0)-aryPred = Formula
(suc n)-aryPred = Term → (n)-aryPred


P : (1)-aryPred
P t = atom (mkrel 1 "P") (t ∷ [])
Px = P x
Py = Px [ x / y ]

∀x ¬∀x ∃x ¬∃x : Formula → Formula
∀x Φ = Λ xvar Φ
∃x Φ = V xvar Φ
¬∀x Φ = ¬(∀x Φ)
¬∃x Φ = ¬(∃x Φ)

∀y ¬∀y ∃y ¬∃y : Formula → Formula
∀y Φ = Λ yvar Φ
∃y Φ = V yvar Φ
¬∀y Φ = ¬(∀y Φ)
¬∃y Φ = ¬(∃y Φ)

lem wlem : Formula → Formula
lem Φ = Φ ∨ ¬ Φ
wlem Φ = ¬ Φ ∨ ¬¬ Φ

lem⊃wlem : [ lem (¬ Q) ] ⊃ wlem Q
lem⊃wlem = axiom (lem (¬ Q))

dp gmp : (1)-aryPred → Formula
dp p = ∃y ((p y) ⇒ ∀x (p x))
gmp p = ¬∀x (p x) ⇒ ∃x (¬(p x))

dp⊃gmp : [ dp P ] ⊃ gmp P
dp⊃gmp = arrowintro (¬∀x Px) (existelim (axiom (dp P)) (existintro y xvar
          (arrowintro {! Py  !} (arrowelim {! assume (¬∀x Px)  !} (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py))))))


