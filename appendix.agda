open import Formula hiding (ident)

open import Decidable
open import Vec

-- Prove that ident is a derived rule. Note that this proof does not make use
-- of Formula.ident
ident : ∀ α x → α [ x / varterm x ]≡ α
ident (atom r ts) x = atom r (identTerms ts x)
  where
    identTerms : ∀{n} → (ts : Vec Term n) → ∀ x → [ ts ][ x / varterm x ]≡ ts
    identTerms [] x = []
    identTerms (varterm y ∷ ts) x with varEq x y
    ...                           | yes refl = varterm≡ ∷ identTerms ts x
    ...                           | no  x≢y  = varterm≢ x≢y ∷ identTerms ts x
    identTerms (functerm f us ∷ ts) x = functerm (identTerms us x) ∷ identTerms ts x
ident (α ⇒ β) x = ident α x ⇒ ident β x
ident (α ∧ β) x = ident α x ∧ ident β x
ident (α ∨ β) x = ident α x ∨ ident β x
ident (Λ y α) x with varEq x y
...             | yes refl = Λ∣ y α
...             | no  x≢y  = Λ x≢y (varterm y≢x) (ident α x)
                             where
                               y≢x : y ≢ x
                               y≢x refl = x≢y refl
ident (V y α) x with varEq x y
...             | yes refl = V∣ y α
...             | no  x≢y  = V x≢y (varterm y≢x) (ident α x)
                             where
                               y≢x : y ≢ x
                               y≢x refl = x≢y refl


-- We have proved that if t is free for x in α then α [ x / t ] exists. The
-- converse is also true, meaning _FreeFor_In_ precisely captures the notion of
-- a substitution being possible.
subFreeFor : ∀{α x t β} → α [ x / t ]≡ β → t FreeFor x In α
subFreeFor (ident (atom r ts) x) = atom r ts
subFreeFor (ident (α ⇒ α₁) x) = subFreeFor (ident α x) ⇒ subFreeFor (ident α₁ x)
subFreeFor (ident (α ∧ α₁) x) = subFreeFor (ident α x) ∧ subFreeFor (ident α₁ x)
subFreeFor (ident (α ∨ α₁) x) = subFreeFor (ident α x) ∨ subFreeFor (ident α₁ x)
subFreeFor (ident (Λ x₁ α) x) with varEq x₁ x
subFreeFor (ident (Λ x₁ α) .x₁) | yes refl = Λ∣ α
subFreeFor (ident (Λ x₁ α) x) | no x₂ = Λ α x₁ (varterm x₂) (subFreeFor (ident α x))
subFreeFor (ident (V x₁ α) x) with varEq x₁ x
subFreeFor (ident (V x₁ α) .x₁) | yes refl = V∣ α
subFreeFor (ident (V x₁ α) x) | no x₂ = V α x₁ (varterm x₂) (subFreeFor (ident α x))
subFreeFor (notfree x) = notfree x
subFreeFor (atom r x) = atom r _
subFreeFor (rep ⇒ rep₁) = subFreeFor rep ⇒ subFreeFor rep₁
subFreeFor (rep ∧ rep₁) = subFreeFor rep ∧ subFreeFor rep₁
subFreeFor (rep ∨ rep₁) = subFreeFor rep ∨ subFreeFor rep₁
subFreeFor (Λ∣ x α) = Λ∣ α
subFreeFor (V∣ x α) = V∣ α
subFreeFor (Λ x x₁ rep) = Λ _ _ x₁ (subFreeFor rep)
subFreeFor (V x x₁ rep) = V _ _ x₁ (subFreeFor rep)
