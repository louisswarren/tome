open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

open import Decidable
open import List
  hiding (All ; all ; Any ; any)
  renaming (
    _∷_        to _[∷]_        ;
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    decide∈    to decide[∈]    )


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

_∷_ : {A : Set} → A → Pred A → Pred A
(α ∷ αs) x = x ≢ α → ¬(x ∉ αs)

_-_ : {A : Set} → Pred A → A → Pred A
(αs - α) x = ¬(x ≢ α → x ∉ αs)

_∪_ : {A : Set} → Pred A → Pred A → Pred A
(αs ∪ βs) x = x ∉ αs → ¬(x ∉ βs)

_⊂_ : {A : Set} → Pred A → Pred A → Set
αs ⊂ βs = ∀ x → x ∈ αs → ¬(x ∉ βs)

data All_⟨_∖_⟩ {A : Set} (P : Pred A) : Pred A → List A → Set₁ where
  all∅ : ∀{xs}       → All P ⟨ ∅ ∖ xs ⟩
  _all∷_  : ∀{αs xs α}  → P α      → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _all-∷_ : ∀{αs xs α}  → α [∈] xs → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _all~_  : ∀{αs xs}    → ∀ x → All P ⟨ αs ∖ x [∷] xs ⟩ → All P ⟨ αs - x ∖ xs ⟩
  _all∪_  : ∀{αs βs xs} → All P ⟨ αs ∖ xs ⟩ → All P ⟨ βs ∖ xs ⟩
                     → All P ⟨ αs ∪ βs ∖ xs ⟩

All : {A : Set} → Pred A → Pred A → Set₁
All P αs = All P ⟨ αs ∖ [] ⟩


test : {A : Set} → (αs : Pred A) → (α : A) → α ∉ (αs - α)
test αs α x = x (λ z _ → z refl)

test2 : {A : Set} → (αs : Pred A) → (α x : A) → α ∉ αs → α ∉ (αs - x)
test2 αs α x α∉αs x₂ = x₂ (λ _ → α∉αs)
