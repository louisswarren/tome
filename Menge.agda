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

infix 4 _∈_ _∉_

_∈_ : {A : Set} → A → Pred A → Set
α ∈ αs = αs α

_∉_ : {A : Set} → A → Pred A → Set
α ∉ αs = ¬(α ∈ αs)

infixr 5 _∪_
infixl 5 _-_

∅ : {A : Set} → Pred A
∅ _ = ⊥

⟨_⟩ : {A : Set} → A → Pred A
⟨ α ⟩ x = x ≡ α

_-_ : {A : Set} → Pred A → A → Pred A
(αs - α) x = ¬(x ≢ α → x ∉ αs)

_∪_ : {A : Set} → Pred A → Pred A → Pred A
(αs ∪ βs) x = x ∉ αs → ¬(x ∉ βs)

_⊂_ : {A : Set} → Pred A → Pred A → Set
αs ⊂ βs = ∀ x → x ∈ αs → ¬(x ∉ βs)

data DecMenge {A : Set} (eq : Decidable≡ A) : Pred A → Set₁ where
  from∅   : DecMenge eq ∅
  from⟨_⟩ : (α : A) → DecMenge eq (⟨ α ⟩)
  from_-_ : ∀{αs} → DecMenge eq αs → (α : A) → DecMenge eq (αs - α)
  from_∪_ : ∀{αs βs} → DecMenge eq αs → DecMenge eq βs → DecMenge eq (αs ∪ βs)

decide∈ : {A : Set} {αs : Pred A}
          → (eq : Decidable≡ A) → (α : A) → DecMenge eq αs → Dec (α ∈ αs)
decide∈ eq x from∅ = no (λ z → z)
decide∈ eq x (from⟨ α ⟩) with eq x α
...                          | yes refl = yes refl
...                          | no x≢α   = eq x α
decide∈ eq x (from dmαs - α) with eq x α
...                          | yes refl = no (λ z → z (λ x x₁ → x refl))
...                          | no x≢α   with decide∈ eq x dmαs
...                                     | yes x₁ = yes (λ x₂ → x₂ x≢α x₁)
...                                     | no x₁ = no (λ z → z (λ x → x₁))
decide∈ eq x (from dmαs ∪ dmβs) with decide∈ eq x dmαs
...                             | yes x₁ = yes (λ x₂ x₃ → x₂ x₁)
...                             | no x₁  with decide∈ eq x dmβs
...                                      | yes x₂ = yes (λ x₃ x₄ → x₄ x₂)
...                                      | no x₂ = no (λ z → z x₁ x₂)


data All_⟨_∖_⟩ {A : Set} (P : Pred A) : Pred A → List A → Set₁ where
  all∅ : ∀{xs}       → All P ⟨ ∅ ∖ xs ⟩
  all⟨_⟩  : ∀{xs α}  → P α     → All P ⟨ ⟨ α ⟩ ∖ xs ⟩
  all-⟨_⟩ : ∀{xs α}  → α [∈] xs → All P ⟨ ⟨ α ⟩ ∖ xs ⟩
  _all~_  : ∀{αs xs}    → ∀ x → All P ⟨ αs ∖ x [∷] xs ⟩ → All P ⟨ αs - x ∖ xs ⟩
  _all∪_  : ∀{αs βs xs} → All P ⟨ αs ∖ xs ⟩ → All P ⟨ βs ∖ xs ⟩
                     → All P ⟨ αs ∪ βs ∖ xs ⟩

All : {A : Set} → Pred A → Pred A → Set₁
All P αs = All P ⟨ αs ∖ [] ⟩


test : {A : Set} → (αs : Pred A) → (α : A) → α ∉ (αs - α)
test αs α x = x (λ z _ → z refl)

test2 : {A : Set} → (αs : Pred A) → (α x : A) → α ∉ αs → α ∉ (αs - x)
test2 αs α x α∉αs x₂ = x₂ (λ _ → α∉αs)
