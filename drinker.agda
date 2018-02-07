open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Deduction
open import Formula
open import Texify

open import common
open import sugar


lem wlem : Formula → Formula
lem  Φ = Φ ∨ ¬ Φ
wlem Φ = ¬ Φ ∨ ¬¬ Φ

dgp : Formula → Formula → Formula
dgp Φ Ψ  = (Φ ⇒ Ψ) ∨ (Ψ ⇒ Φ)

glpo glpoa gmp  : Variable → Formula → Formula
glpo  v f = ∀x ¬Φ ∨ ∃x Φ                        where Φ = f [! v / x ]; ¬Φ = ¬ Φ
glpoa v f = ∀x Φ ∨ ∃x ¬Φ                        where Φ = f [! v / x ]; ¬Φ = ¬ Φ
gmp   v f = ¬∀x Φ ⇒ ∃x ¬Φ                       where Φ = f [! v / x ]; ¬Φ = ¬ Φ

-- Requires that v isNotFreeIn [ Ψ ]
uds : (v : Variable) → Formula → (Ψ : Formula) → Formula
uds v f Ψ = ∀x (Φ ∨ Ψ) ⇒ (∀x Φ ∨ Ψ)             where Φ = f [! v / x ]; ¬Φ = ¬ Φ

ud : Variable →  Scheme
ud v = scheme 2 "UD" (vecfunc2 (uds v)) ([] ∷ [ v ] ∷ [])
