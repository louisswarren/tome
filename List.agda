module List where

open import Agda.Builtin.List public
open import Decidable

infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


data All {A : Set} (P : Pred A) : List A → Set where
  []  : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

private
  -- Some lemmae for All
  headAll : ∀{A x xs} {P : Pred A} → All P (x ∷ xs) → P x
  headAll (Px ∷ _) = Px

  tailAll : ∀{A x xs} {P : Pred A} → All P (x ∷ xs) → All P xs
  tailAll (_ ∷ ∀xsP) = ∀xsP

-- All is decidable for decidable predicates
all : {A : Set} {P : Pred A} → (P? : Decidable P) → (xs : List A) → Dec (All P xs)
all P? [] = yes []
all P? (x ∷ xs) with P? x
...             | no ¬Px = no λ φ → ¬Px (headAll φ)
...             | yes Px with all P? xs
...                      | yes ∀xsP = yes (Px ∷ ∀xsP)
...                      | no ¬∀xsP = no λ φ → ¬∀xsP (tailAll φ)


infixr 5 _∷_

data Any {A : Set} (P : Pred A) : List A → Set where
  [_] : ∀{xs} → ∀{x} → P x      → Any P (x ∷ xs)
  _∷_ : ∀{xs} → ∀ x  → Any P xs → Any P (x ∷ xs)

private
  -- Some lemmae for Any
  hereAny : ∀{A x xs} {P : Pred A} → Any P (x ∷ xs) → ¬(Any P xs) → P x
  hereAny [ Px ]     ¬∃xsP = Px
  hereAny (_ ∷ ∃xsP) ¬∃xsP = ⊥-elim (¬∃xsP ∃xsP)

  laterAny : ∀{A x xs} {P : Pred A} → Any P (x ∷ xs) → ¬(P x) → (Any P xs)
  laterAny [ Px ]     ¬Px = ⊥-elim (¬Px Px)
  laterAny (_ ∷ ∃xsP) ¬Px = ∃xsP

-- Any is decidable for decidable predicates
any : {A : Set} {P : Pred A} → (P? : Decidable P) → (xs : List A) → Dec (Any P xs)
any P? [] = no (λ ())
any P? (x ∷ xs) with P? x
...             | yes Px = yes [ Px ]
...             | no ¬Px with any P? xs
...                      | yes ∃xsP = yes (x ∷ ∃xsP)
...                      | no ¬∃xsP = no λ φ → ¬Px (hereAny φ ¬∃xsP)


-- Any can be used to define membership
infix 4 _∈_ _∉_

_∈_ : {A : Set} → (x : A) → List A → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → (x : A) → List A → Set
x ∉ xs = ¬(x ∈ xs)

-- Memberhsip is decidable if equality is decidable.
decide∈ : {A : Set} → Decidable≡ A → (x : A) → (xs : List A) → Dec (x ∈ xs)
decide∈ _≟_ x xs = any (x ≟_) xs
