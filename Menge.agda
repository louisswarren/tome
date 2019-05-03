open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

open import Decidable
open import List using (List ; [] ; _∷_)

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


data Assembled {A : Set} (eq : Decidable≡ A) : Pred A → Set₁ where
  from∅   : Assembled eq ∅
  from⟨_⟩ : (α : A) → Assembled eq (⟨ α ⟩)
  from_-_ : ∀{αs} → Assembled eq αs → (α : A) → Assembled eq (αs - α)
  from_∪_ : ∀{αs βs} → Assembled eq αs → Assembled eq βs → Assembled eq (αs ∪ βs)


decide∈ : {A : Set} {eq : Decidable≡ A} {αs : Pred A}
          → (x : A) → Assembled eq αs → Dec (x ∈ αs)
decide∈ x from∅ = no λ x∈∅ → x∈∅
decide∈ {A} {eq} x (from⟨ α ⟩) with eq x α
...                            | yes refl = yes refl
...                            | no x≢α   = eq x α
decide∈ {A} {eq} x (from Aαs - α) with eq x α
...                               | yes refl = no λ α∈αs-α → α∈αs-α λ α≢α _ → α≢α refl
...                               | no x≢α   with decide∈ x Aαs
...                                          | yes x∈αs = yes λ x≢α→x∉αs → x≢α→x∉αs x≢α x∈αs
...                                          | no  x∉αs = no  λ x∈αs-α → x∈αs-α λ _ _ → x∈αs-α λ _ _ → x∈αs-α (λ _ → x∉αs)
decide∈ x (from Aαs ∪ Aβs) with decide∈ x Aαs
...                        | yes x∈αs = yes λ x∉αs _ → x∉αs x∈αs
...                        | no  x∉αs with decide∈ x Aβs
...                                   | yes x∈βs = yes λ _ x∉βs → x∉βs x∈βs
...                                   | no  x∉βs = no λ x∉αs∪βs → x∉αs∪βs x∉αs x∉βs


infixr 5 _all∪_
infixl 5 _all~_

data All_[_∖_] {A : Set} (P : Pred A) : Pred A → List A → Set₁ where
  all∅    : ∀{xs}    → All P [ ∅ ∖ xs ]
  all⟨_⟩  : ∀{xs α}  → P α         → All P [ ⟨ α ⟩ ∖ xs ]
  all-_   : ∀{xs α}  → α List.∈ xs → All P [ ⟨ α ⟩ ∖ xs ]
  _all~_  : ∀{αs xs} → ∀ x → All P [ αs ∖ x ∷ xs ] → All P [ αs - x ∖ xs ]
  _all∪_  : ∀{αs βs xs}
              → All P [ αs ∖ xs ] → All P [ βs ∖ xs ] → All P [ αs ∪ βs ∖ xs ]

All : {A : Set} → Pred A → Pred A → Set₁
All P αs = All P [ αs ∖ [] ]
