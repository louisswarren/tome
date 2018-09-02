open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String
open import Agda.Builtin.List

open import Formula
open import Vec

⊥ : Formula
⊥ = atom (mkprop 0) []

¬ ¬¬ : Formula → Formula
¬ α = α ⇒ ⊥
¬¬ α = ¬ (¬ α)


nullaryscheme : String → Formula → Scheme
nullaryscheme s f = scheme s 0 fs
                    where
                      fs : _
                      fs [] = f

unaryscheme : String → (Formula → Formula) → Scheme
unaryscheme s f = scheme s 1 fs
                  where
                    fs : _
                    fs (α ∷ []) = f α

binaryscheme : String → (Formula → Formula → Formula) → Scheme
binaryscheme s f = scheme s 2 fs
                   where
                     fs : _
                     fs (α ∷ β ∷ []) = f α β


pattern xvar  = mkvar 0
pattern yvar  = mkvar 1
pattern zvar  = mkvar 2
pattern var n = mkvar (suc (suc (suc n)))

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
