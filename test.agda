open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Formula
open import Deduction
open import Texify
open import common
open import sugar

Q = atom (mkprop "Q") []
P : Term → Formula
P t = atom (mkrel 1 "P") (t ∷ [])

Px = P x
Py = P y
--------------------------------------------------------------------------------

lemf : Vec Formula 1 → Formula
lemf (α ∷ []) = α ∨ ¬ α
lem : Scheme
lem = scheme 1 "LEM" lemf ([] ∷ [])

dgpf : Vec Formula 2 → Formula
dgpf (α ∷ β ∷ []) = (α ⇒ β) ∨ (β ⇒ α)
dgp : Scheme
dgp = scheme 2 "DGP" dgpf ([] ∷ [] ∷ [])

dpf : Vec Formula 1 → Formula
dpf (α ∷ []) = ∃y ((α [ x / y ]) ⇒ (∀x α))
dp : Scheme
dp = scheme 1 "DP" dpf ([] ∷ [])

gmpf : Vec Formula 1 → Formula
gmpf (α ∷ []) = ¬ (∀x α) ⇒ ∃x (¬ α)
gmp : Scheme
gmp = scheme 1 "GMP" gmpf ([] ∷ [])


pf : dgp ∷ lem ∷ [] , [] ⊢ Q ∨ ¬ Q
pf = axiom 1 (Q ∷ [])


pf2 : dp ∷ [] , [] ⊢ gmpf (P x ∷ [])
pf2 = arrowintro (¬∀x Px)
          (existelim
           (axiom 0 (Px ∷ []))
           (existintro y xvar (arrowintro Py
            (arrowelim (assume (¬∀x Px))
             (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))))
           )

s = texify pf2




-- Let's do that again, but not assume that x is the free variable

dpsf : Variable → Vec Formula 1 → Formula
dpsf v (α ∷ []) = ∃y ((α [ varterm v / y ]) ⇒ (∀x (α [ varterm v / x ])))
dps : Variable → Scheme
dps v = scheme 1 "DP" (dpsf v) ([] ∷ [])

gmpsf : Variable → Vec Formula 1 → Formula
gmpsf v (α ∷ []) = ¬ (∀x (α [ varterm v / x ])) ⇒ ∃x (¬ (α [ varterm v / x ]))
gmps : Variable → Scheme
gmps v = scheme 1 "GMP" (gmpsf v) ([] ∷ [])


pf3 : (dps xvar) ∷ [] , [] ⊢ gmpsf xvar (P x ∷ [])
pf3 = arrowintro (¬∀x Px)
          (existelim
           (axiom 0 (Px ∷ []))
           (existintro y xvar (arrowintro Py
            (arrowelim (assume (¬∀x Px))
             (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))))
           )

-- Requires that {_ : v isNotFreeIn [ Ψ ]}
uds : (v : Variable) → Formula → (Ψ : Formula) → Formula
uds v f Ψ = ∀x (Φ ∨ Ψ) ⇒ (∀x Φ ∨ Ψ)             where Φ = f [! v / x ]; ¬Φ = ¬ Φ

ud : Variable →  Scheme
ud v = scheme 2 "UD" (vecfunc2 (uds v)) ([] ∷ [ v ] ∷ [])


reqtest : [ ud xvar ] , [] ⊢ uds xvar (P x) Q
reqtest = axiom 0 (P x ∷ Q ∷ [])

-- This won't work: Agda can't prove that x is not free in Px (since it's false)
-- reqtest2 : [ ud xvar ] , [] ⊢ uds xvar Q (P x)
-- reqtest2 = axiom 0 (Q ∷ P x ∷ [])
