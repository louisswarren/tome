open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Deduction
open import Formula
open import Texify

open import common
open import sugar

GLPO GLPOA GMP UD : Variable → Scheme
LEM WLEM DGP : Scheme

lem wlem : Formula → Formula
lem  Φ = Φ ∨ ¬ Φ
wlem Φ = ¬ Φ ∨ ¬¬ Φ

LEM  = unaryscheme "LEM" lem
WLEM = unaryscheme "WLEM" wlem



dgp : Formula → Formula → Formula
dgp Φ Ψ  = (Φ ⇒ Ψ) ∨ (Ψ ⇒ Φ)

DGP = binaryscheme "DGP" dgp



glpo glpoa gmp  : Variable → Formula → Formula
glpo  v f = ∀x ¬Φ ∨ ∃x Φ                        where Φ = f [! v / x ]; ¬Φ = ¬ Φ
glpoa v f = ∀x Φ ∨ ∃x ¬Φ                        where Φ = f [! v / x ]; ¬Φ = ¬ Φ
gmp   v f = ¬∀x Φ ⇒ ∃x ¬Φ                       where Φ = f [! v / x ]; ¬Φ = ¬ Φ

GLPO  v = unaryscheme "GLPO"  (glpo v)
GLPOA v = unaryscheme "GLPOA" (glpoa v)
GMP   v = unaryscheme "GMP"   (gmp v)



-- Requires that v isNotFreeIn [ Ψ ]
ud : (v : Variable) → Formula → (Ψ : Formula) → Formula
ud v f Ψ = ∀x (Φ ∨ Ψ) ⇒ (∀x Φ ∨ Ψ)             where Φ = f [! v / x ]; ¬Φ = ¬ Φ

UD v = scheme 2 "UD" (vecfunc2 (ud v)) ([] ∷ [ v ] ∷ [])
