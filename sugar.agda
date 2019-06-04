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


-- Easier definitions for derivability
infix 1 ⊢₀_ ⊢₁_ ⊢₂_

⊢₀_ : Formula → Set₁
⊢₀ α = ⊢ α

⊢₁_ : (Formula → Formula) → Set₁
⊢₁ s = ∀ α → ⊢ s α

⊢₂_ : (Formula → Formula → Formula) → Set₁
⊢₂ s = ∀ α β → ⊢ s α β

descheme₀ : {f : Vec Formula 0 → Formula}
            → (∀ αs → ⊢ f αs) → ⊢ f []
descheme₀ {f} ⊢S = ⊢S []

descheme₁ : {f : Vec Formula 1 → Formula}
            → (∀ αs → ⊢ f αs) → ∀ α → ⊢ f (α ∷ [])
descheme₁ {f} ⊢S α = ⊢S (α ∷ [])

descheme₂ : {f : Vec Formula 2 → Formula}
            → (∀ αs → ⊢ f αs) → ∀ α β → ⊢ f (α ∷ β ∷ [])
descheme₂ {f} ⊢S α β = ⊢S (α ∷ (β ∷ []))


-- Fix a few formula components
pattern xvar   = var zero
pattern yvar   = var (suc zero)
pattern zvar   = var (suc (suc zero))
pattern nvar n = var (suc (suc (suc n)))

x y z : Term
x = varterm xvar
y = varterm yvar
z = varterm zvar

pattern Arel = rel (suc zero)                         zero
pattern Brel = rel (suc (suc zero))                   zero
pattern Crel = rel (suc (suc (suc zero)))             zero
pattern Prel = rel (suc (suc (suc (suc zero))))       (suc zero)
pattern Qrel = rel (suc (suc (suc (suc (suc zero))))) (suc zero)

pattern A = atom Arel []
pattern B = atom Brel []
pattern C = atom Crel []

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
