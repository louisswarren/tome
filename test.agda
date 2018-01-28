open import Agda.Builtin.List
open import Agda.Builtin.String

open import Formula
open import Deduction

P = propatom (mkprop "P")
Q = propatom (mkprop "Q")

lem wlem : Formula → Formula
lem Φ = Φ ∨ ¬ Φ
wlem Φ = ¬ Φ ∨ ¬¬ Φ

lem⊃wlem : [ lem (¬ P) ] ⊃ wlem P
lem⊃wlem = axiom (lem (¬ P))


