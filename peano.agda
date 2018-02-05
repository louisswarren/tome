open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Formula
open import Deduction
open import Texify
open import common

xvar yvar zvar : Variable
xvar = mkvar "x"
yvar = mkvar "y"
zvar = mkvar "z"

x = varterm xvar
y = varterm yvar
z = varterm zvar

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

∀z ¬∀z ∃z ¬∃z : Formula → Formula
∀z Φ = Λ zvar Φ
∃z Φ = V zvar Φ
¬∀z Φ = ¬(∀z Φ)
¬∃z Φ = ¬(∃z Φ)

--------------------------------------------------------------------------------

-- Peano primatives
ppzero  = mkconst "zero"
ppsuc   = mkfunc 1 "suc"
ppeqs   = mkrel 2 "eq"
ppisnat = mkrel 1 "isnat"

-- Peano syntax sugar
pzero = functerm ppzero []

psuc : Term → Term
psuc t = functerm ppsuc (t ∷ [])

_≈_ : Term → Term → Formula
s ≈ t = atom ppeqs (s ∷ t ∷ [])
infixr 1000 _≈_

pisnat : Term → Formula
pisnat t = atom ppisnat (t ∷ [])


-- Peano axioms
-- All but induction are 0-ary schemes
pax1 = nullaryscheme "Pzero" (pisnat pzero)
pax2 = nullaryscheme "Prefl" (∀x (x ≈ x))
pax3 = nullaryscheme "Psymm" (∀x (∀y (x ≈ y ⇒ y ≈ x)))
pax4 = nullaryscheme "Ptran" (∀x (∀y (∀z (x ≈ y ⇒ y ≈ x ⇒ x ≈ z))))
pax5 = nullaryscheme "Pclos" (∀x (∀y (pisnat x ⇒ x ≈ y ⇒ pisnat y)))
pax6 = nullaryscheme "Psucn" (∀x (pisnat x ⇔ pisnat (psuc x)))
pax7 = nullaryscheme "Psucc" (∀x (∀y (x ≈ y ⇒ psuc x ≈ psuc y)))
pax8 = nullaryscheme "Pinfi" (∀x (¬ (psuc x ≈ pzero)))

-- For simplicity, include a parametrised induction by the free variable

induction : Variable → Vec Formula 1 → Formula
induction v (α ∷ []) = (α [ varterm v / pzero ])
                       ⇒ V v (pisnat (varterm v)
                              ⇒ α
                              ⇒ (α [ varterm v / psuc (varterm v) ]))
                       ⇒ V v α
pax9fv : Variable → Scheme
pax9fv v = scheme 1 "Pindu" (induction v)

pax9 = pax9fv xvar

-- Axiom required in minimal logic for collapsing arithmetic absurdities
paxm = nullaryscheme "Pmini" (∀x (psuc x ≈ pzero ⇒ psuc pzero ≈ pzero))
