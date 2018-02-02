open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Formula
open import Deduction
open import Scheme
open import Texify
open import common

Q = propatom (mkprop "Q")
P : Term → Formula
P t = atom (mkrel 1 "P") (t ∷ [])

xvar yvar : Variable
xvar = mkvar "x"
yvar = mkvar "y"

x = varterm xvar
y = varterm yvar

--------------------------------------------------------------------------------
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

Px = P x
Py = P y
--------------------------------------------------------------------------------

lemf : Vec Formula 1 → Formula
lemf (α ∷ []) = α ∨ ¬ α
lem : Scheme
lem = record { arity = 1; name = "LEM"; func = lemf }

dgpf : Vec Formula 2 → Formula
dgpf (α ∷ β ∷ []) = (α ⇒ β) ∨ (β ⇒ α)
dgp : Scheme
dgp = record { arity = 2; name = "DGP"; func = dgpf }

dpf : Vec Formula 1 → Formula
dpf (α ∷ []) = ∃y ((α [ x / y ]) ⇒ (∀x α))
dp : Scheme
dp = record { arity = 1; name = "DP"; func = dpf }

gmpf : Vec Formula 1 → Formula
gmpf (α ∷ []) = ¬ (∀x α) ⇒ ∃x (¬ α)
gmp : Scheme
gmp = record { arity = 1; name = "GMP"; func = gmpf }


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
dps v = record { name = "DP"; func = (dpsf v) }

gmpsf : Variable → Vec Formula 1 → Formula
gmpsf v (α ∷ []) = ¬ (∀x (α [ varterm v / x ])) ⇒ ∃x (¬ (α [ varterm v / x ]))
gmps : Variable → Scheme
gmps v = record { name = "GMP"; func = (gmpsf v) }


pf3 : (dps xvar) ∷ [] , [] ⊢ gmpsf xvar (P x ∷ [])
pf3 = arrowintro (¬∀x Px)
          (existelim
           (axiom 0 (Px ∷ []))
           (existintro y xvar (arrowintro Py
            (arrowelim (assume (¬∀x Px))
             (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))))
           )
