open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

open import Decidable

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

infix 4 _∈_ _∉_

_∈_ : {A : Set} → A → Pred A → Set
α ∈ αs = αs α

_∉_ : {A : Set} → A → Pred A → Set
α ∉ αs = ¬(α ∈ αs)

infixr 5 _∷_ _∪_
infixl 5 _-_

∅ : {A : Set} → Pred A
∅ _ = ⊥

--_∷_ : {A : Set} → A → Pred A → Pred A
--(α ∷ αs) x = (α ≡ x) ⊎ (x ∈ αs)
--
--_-_ : {A : Set} → Pred A → A → Pred A
--(αs - α) x = (α ≢ x) × (x ∈ αs)
--
--_∪_ : {A : Set} → Pred A → Pred A → Pred A
--(αs ∪ βs) x = (x ∈ αs) ⊎ (x ∈ βs)

_∷_ : {A : Set} → A → Pred A → Pred A
(α ∷ αs) x = x ≢ α → x ∈ αs

_-_ : {A : Set} → Pred A → A → Pred A
(αs - α) x = ¬(x ∈ αs → x ≡ α)

_∪_ : {A : Set} → Pred A → Pred A → Pred A
(αs ∪ βs) x = x ∉ αs → x ∈ βs

All : {A : Set} → Pred A → Pred A → Set
All P αs = ∀ x → x ∈ αs → P x

Any : {A : Set} → Pred A → Pred A → Set
Any P αs = Σ _ λ x → P x × (x ∈ αs)

_⊂_ : {A : Set} → Pred A → Pred A → Set
αs ⊂ βs = ∀ x → x ∈ αs → x ∈ βs


test : {A : Set} → (αs : Pred A) → (α : A) → α ∉ (αs - α)
test αs α x = x (λ _ → refl)

test2 : {A : Set} → (αs : Pred A) → (α x : A) → α ∉ αs → α ∉ (αs - x)
test2 αs α x α∉αs x₂ = x₂ (λ z → ⊥-elim (α∉αs z))
