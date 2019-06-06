module Sugar where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String
open import Agda.Builtin.List

open import Deduction
open import Formula
open import Vec


-- We use pattern extensively so that Agda fills in the sugar

-- Define negation
pattern ⊥rel = rel zero zero
pattern ⊥ = atom ⊥rel []

pattern ¬ α = α ⇒ ⊥
pattern ¬¬ α = ¬ (¬ α)

-- Fix a few formula components
pattern xvar   = var zero
pattern yvar   = var (suc zero)
pattern zvar   = var (suc (suc zero))
pattern nvar n = var (suc (suc (suc n)))

x y z : Term
x = varterm xvar
y = varterm yvar
z = varterm zvar

pattern t0 = functerm (func 0 0) []
pattern t1 = functerm (func 1 0) []
pattern t2 = functerm (func 2 0) []
pattern t3 = functerm (func 3 0) []
pattern t4 = functerm (func 4 0) []
pattern t5 = functerm (func 5 0) []

pattern Arel = rel (suc zero)                               zero
pattern Brel = rel (suc (suc zero))                         zero
pattern Crel = rel (suc (suc (suc zero)))                   zero
pattern Drel = rel (suc (suc (suc (suc zero))))             (suc zero)
pattern Prel = rel (suc (suc (suc (suc (suc zero)))))       (suc zero)
pattern Qrel = rel (suc (suc (suc (suc (suc (suc zero)))))) (suc zero)

pattern A = atom Arel []
pattern B = atom Brel []
pattern C = atom Crel []

pattern D t = atom Drel (t ∷ [])
pattern P t = atom Prel (t ∷ [])
pattern Q t = atom Qrel (t ∷ [])

-- Nice generalisation notation
pattern ∀x Φ = Λ xvar Φ
pattern ∃x Φ = V xvar Φ
pattern ∀x¬ Φ = ∀x (¬ Φ)
pattern ∃x¬ Φ = ∃x (¬ Φ)
pattern ∀x¬¬ Φ = ∀x (¬¬ Φ)
pattern ∃x¬¬ Φ = ∃x (¬¬ Φ)
pattern ¬∀x Φ = ¬(∀x Φ)
pattern ¬∃x Φ = ¬(∃x Φ)
pattern ¬∀x¬ Φ = ¬(∀x¬ Φ)
pattern ¬∃x¬ Φ = ¬(∃x¬ Φ)
pattern ¬∀x¬¬ Φ = ¬(∀x¬¬ Φ)
pattern ¬∃x¬¬ Φ = ¬(∃x¬¬ Φ)
pattern ¬¬∀x Φ = ¬¬(∀x Φ)
pattern ¬¬∃x Φ = ¬¬(∃x Φ)
pattern ¬¬∀x¬ Φ = ¬¬(∀x¬ Φ)
pattern ¬¬∃x¬ Φ = ¬¬(∃x¬ Φ)
pattern ¬¬∀x¬¬ Φ = ¬¬(∀x¬¬ Φ)
pattern ¬¬∃x¬¬ Φ = ¬¬(∃x¬¬ Φ)

pattern ∀y Φ = Λ yvar Φ
pattern ∃y Φ = V yvar Φ
pattern ∀y¬ Φ = ∀y (¬ Φ)
pattern ∃y¬ Φ = ∃y (¬ Φ)
pattern ∀y¬¬ Φ = ∀y (¬¬ Φ)
pattern ∃y¬¬ Φ = ∃y (¬¬ Φ)
pattern ¬∀y Φ = ¬(∀y Φ)
pattern ¬∃y Φ = ¬(∃y Φ)
pattern ¬∀y¬ Φ = ¬(∀y¬ Φ)
pattern ¬∃y¬ Φ = ¬(∃y¬ Φ)
pattern ¬∀y¬¬ Φ = ¬(∀y¬¬ Φ)
pattern ¬∃y¬¬ Φ = ¬(∃y¬¬ Φ)
pattern ¬¬∀y Φ = ¬¬(∀y Φ)
pattern ¬¬∃y Φ = ¬¬(∃y Φ)
pattern ¬¬∀y¬ Φ = ¬¬(∀y¬ Φ)
pattern ¬¬∃y¬ Φ = ¬¬(∃y¬ Φ)
pattern ¬¬∀y¬¬ Φ = ¬¬(∀y¬¬ Φ)
pattern ¬¬∃y¬¬ Φ = ¬¬(∃y¬¬ Φ)

pattern ∀z Φ = Λ zvar Φ
pattern ∃z Φ = V zvar Φ
pattern ∀z¬ Φ = ∀z (¬ Φ)
pattern ∃z¬ Φ = ∃z (¬ Φ)
pattern ∀z¬¬ Φ = ∀z (¬¬ Φ)
pattern ∃z¬¬ Φ = ∃z (¬¬ Φ)
pattern ¬∀z Φ = ¬(∀z Φ)
pattern ¬∃z Φ = ¬(∃z Φ)
pattern ¬∀z¬ Φ = ¬(∀z¬ Φ)
pattern ¬∃z¬ Φ = ¬(∃z¬ Φ)
pattern ¬∀z¬¬ Φ = ¬(∀z¬¬ Φ)
pattern ¬∃z¬¬ Φ = ¬(∃z¬¬ Φ)
pattern ¬¬∀z Φ = ¬¬(∀z Φ)
pattern ¬¬∃z Φ = ¬¬(∃z Φ)
pattern ¬¬∀z¬ Φ = ¬¬(∀z¬ Φ)
pattern ¬¬∃z¬ Φ = ¬¬(∃z¬ Φ)
pattern ¬¬∀z¬¬ Φ = ¬¬(∀z¬¬ Φ)
pattern ¬¬∃z¬¬ Φ = ¬¬(∃z¬¬ Φ)
