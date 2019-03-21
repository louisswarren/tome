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


-- Easier constructors for schemes
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


-- Easier definitions for derivability
infix 1 ⊢₀_ ⊢₁_ ⊢₂_

⊢₀_ : Formula → Set
⊢₀ α = ⊢ α

⊢₁_ : (Formula → Formula) → Set
⊢₁ s = ∀ α → ⊢ s α

⊢₂_ : (Formula → Formula → Formula) → Set
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

private
  _>>_ = primStringAppend
  infixr 1 _>>_


-- Stdlib show is broken on my computer
strnum : ℕ → String
strnum zero = "0"
strnum (suc n) = "s(" >> strnum n >> ")"

strrel : Relation → String
strrel (rel 0 k) = "\\bot"
strrel (rel 1 k) = "A"
strrel (rel 2 k) = "B"
strrel (rel 3 k) = "C"
strrel (rel 4 k) = "P"
strrel (rel 5 k) = "Q"
strrel (rel (suc (suc (suc (suc (suc (suc n)))))) k) = "R_" >> strnum n

strvar : Variable → String
strvar xvar = "x"
strvar yvar = "y"
strvar zvar = "z"
strvar (var n) = "v_" >> strnum n

strfunc : Function → String
strfunc (func n k) = "f_" >> strnum n



-- Nice generalisation notation
pattern ∀x Φ = Λ xvar Φ
pattern ∃x Φ = V xvar Φ
pattern ∀x¬ Φ = ∀x (¬ Φ)
pattern ∃x¬ Φ = ∃x (¬ Φ)
pattern ¬∀x Φ = ¬(∀x Φ)
pattern ¬∃x Φ = ¬(∃x Φ)
pattern ¬∀x¬ Φ = ¬(∀x¬ Φ)
pattern ¬∃x¬ Φ = ¬(∃x¬ Φ)

pattern ∀y Φ = Λ yvar Φ
pattern ∃y Φ = V yvar Φ
pattern ∀y¬ Φ = ∀y (¬ Φ)
pattern ∃y¬ Φ = ∃y (¬ Φ)
pattern ¬∀y Φ = ¬(∀y Φ)
pattern ¬∃y Φ = ¬(∃y Φ)
pattern ¬∀y¬ Φ = ¬(∀y¬ Φ)
pattern ¬∃y¬ Φ = ¬(∃y¬ Φ)

pattern ∀z Φ = Λ zvar Φ
pattern ∃z Φ = V zvar Φ
pattern ∀z¬ Φ = ∀z (¬ Φ)
pattern ∃z¬ Φ = ∃z (¬ Φ)
pattern ¬∀z Φ = ¬(∀z Φ)
pattern ¬∃z Φ = ¬(∃z Φ)
pattern ¬∀z¬ Φ = ¬(∀z¬ Φ)
pattern ¬∃z¬ Φ = ¬(∃z¬ Φ)
