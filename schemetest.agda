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
lem : (1)-aryScheme
lem = record { name = "LEM"; func = lemf }

dgpf : Vec Formula 2 → Formula
dgpf (α ∷ β ∷ []) = (α ⇒ β) ∨ (β ⇒ α)
dgp : (2)-aryScheme
dgp = record { name = "DGP"; func = dgpf }

dpf : Vec Formula 1 → Formula
dpf (α ∷ []) = ∃y ((α [ x / y ]) ⇒ (∀x α))
dp : (1)-aryScheme
dp = record { name = "DP"; func = dpf }

gmpf : Vec Formula 1 → Formula
gmpf (α ∷ []) = ¬ (∀x α) ⇒ ∃x (¬ α)
gmp : (1)-aryScheme
gmp = record { name = "GMP"; func = gmpf }

Ax : ∀{n k} → (n)-aryScheme → Vec ΣScheme k → Vec ΣScheme (suc k)
Ax {n} x xs = (n ↦ x) ∷ xs


pf : Ax dgp (Ax lem []) , [] ⊢ Q ∨ ¬ Q
pf = axiom 1 (Q ∷ [])


pf2 : Ax dp [] , [] ⊢ gmpf (P x ∷ [])
pf2 = arrowintro (¬∀x Px)
          (existelim
           (axiom 0 (Px ∷ []))
           (existintro y xvar (arrowintro Py
            (arrowelim (assume (¬∀x Px))
             (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))))
           )

s = texify pf2
