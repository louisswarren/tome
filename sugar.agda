open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String
open import Agda.Builtin.List

open import Formula
open import Vec


-- Define negation
⊥ : Formula
⊥ = atom (mkprop 0) []

¬ ¬¬ : Formula → Formula
¬ α = α ⇒ ⊥
¬¬ α = ¬ (¬ α)


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


-- Fix a few formula components
pattern xvar  = mkvar zero
pattern yvar  = mkvar (suc zero)
pattern zvar  = mkvar (suc (suc zero))
pattern var n = mkvar (suc (suc (suc n)))

x = varterm xvar
y = varterm yvar
z = varterm zvar

pattern Arel = mkrel (suc zero)                         zero
pattern Brel = mkrel (suc (suc zero))                   zero
pattern Crel = mkrel (suc (suc (suc zero)))             zero
pattern Prel = mkrel (suc (suc (suc (suc zero))))       (suc zero)
pattern Qrel = mkrel (suc (suc (suc (suc (suc zero))))) (suc zero)

A B C : Formula
A = atom Arel []
B = atom Brel []
C = atom Crel []

P Q : Term → Formula
P t = atom Prel (t ∷ [])
Q t = atom Qrel (t ∷ [])

private
  _>>_ = primStringAppend
  infixr 1 _>>_


-- Stdlib show is broken on my computer
strnum : ℕ → String
strnum zero = "0"
strnum (suc n) = "s(" >> strnum n >> ")"

strrel : Relation → String
strrel (mkrel 0 k) = "\\bot"
strrel (mkrel 1 k) = "A"
strrel (mkrel 2 k) = "B"
strrel (mkrel 3 k) = "C"
strrel (mkrel 4 k) = "P"
strrel (mkrel 5 k) = "Q"
strrel (mkrel (suc (suc (suc (suc (suc (suc n)))))) k) = "R_" >> strnum n

strvar : Variable → String
strvar xvar = "x"
strvar yvar = "y"
strvar zvar = "z"
strvar (var n) = "v_" >> strnum n

strfunc : Function → String
strfunc (mkfunc n k) = "f_" >> strnum n


-- Nice generalisation notation
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
