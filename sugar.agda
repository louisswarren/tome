open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String
open import Agda.Builtin.List

open import Formula

open import common

_[!_/_] : Formula → Variable → Term → Formula
α [! v / t ] = α [ varterm v / t ]

vecfunc2 : {A B : Set} → (A → A → B) → Vec A 2 → B
vecfunc2 f = λ xs → f (xs !! 0) (xs !! 1)

nullaryscheme : String → Formula → Scheme
nullaryscheme s α = scheme zero s (λ _ → α) []

unaryscheme : String → (Formula → Formula) → Scheme
unaryscheme s f = scheme 1 s (λ xs → f (xs !! 0)) ([] ∷ [])

binaryscheme : String → (Formula → Formula → Formula) → Scheme
binaryscheme s f = scheme 2 s (λ xs → f (xs !! 0) (xs !! 1)) ([] ∷ [] ∷ [])



xvar yvar zvar : Variable
xvar = mkvar "x"
yvar = mkvar "y"
zvar = mkvar "z"

x = varterm xvar
y = varterm yvar
z = varterm zvar

∀x ∃x ∀x¬ ∃x¬ ¬∀x ¬∃x ¬∀x¬ ¬∃x¬ : Formula → Formula
∀x Φ = Λ xvar Φ
∃x Φ = V xvar Φ
∀x¬ Φ = ∀x (¬ Φ)
∃x¬ Φ = ∃x (¬ Φ)
¬∀x Φ = ¬(∀x Φ)
¬∃x Φ = ¬(∃x Φ)
¬∀x¬ Φ = ¬(∀x¬ Φ)
¬∃x¬ Φ = ¬(∃x¬ Φ)

∀y ∃y ∀y¬ ∃y¬ ¬∀y ¬∃y ¬∀y¬ ¬∃y¬ : Formula → Formula
∀y Φ = Λ yvar Φ
∃y Φ = V yvar Φ
∀y¬ Φ = ∀y (¬ Φ)
∃y¬ Φ = ∃y (¬ Φ)
¬∀y Φ = ¬(∀y Φ)
¬∃y Φ = ¬(∃y Φ)
¬∀y¬ Φ = ¬(∀y¬ Φ)
¬∃y¬ Φ = ¬(∃y¬ Φ)

∀z ∃z ∀z¬ ∃z¬ ¬∀z ¬∃z ¬∀z¬ ¬∃z¬ : Formula → Formula
∀z Φ = Λ zvar Φ
∃z Φ = V zvar Φ
∀z¬ Φ = ∀z (¬ Φ)
∃z¬ Φ = ∃z (¬ Φ)
¬∀z Φ = ¬(∀z Φ)
¬∃z Φ = ¬(∃z Φ)
¬∀z¬ Φ = ¬(∀z¬ Φ)
¬∃z¬ Φ = ¬(∃z¬ Φ)
