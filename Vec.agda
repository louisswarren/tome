module Vec where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Decidable

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)


data All {A : Set} (P : Pred A) : ∀{n} → Vec A n → Set where
  []  : All P []
  _∷_ : ∀{x n} {xs : Vec A n} → P x → All P xs → All P (x ∷ xs)

private
  -- Some lemmae for All
  headAll : ∀{A x n} {xs : Vec A n} {P : Pred A} → All P (x ∷ xs) → P x
  headAll (Px ∷ _) = Px

  tailAll : ∀{A x n} {xs : Vec A n} {P : Pred A} → All P (x ∷ xs) → All P xs
  tailAll (_ ∷ ∀xsP) = ∀xsP

-- All is decidable for decidable predicates
all : {A : Set} {n : ℕ} {P : Pred A} → (P? : Decidable P) → (xs : Vec A n) → Dec (All P xs)
all P? [] = yes []
all P? (x ∷ xs) with P? x
...             | no ¬Px = no λ φ → ¬Px (headAll φ)
...             | yes Px with all P? xs
...                      | yes ∀xsP = yes (Px ∷ ∀xsP)
...                      | no ¬∀xsP = no λ φ → ¬∀xsP (tailAll φ)


infixr 5 _∷_

data Any {A : Set} (P : Pred A) : ∀{n} → Vec A n → Set where
  [_] : ∀{n} {xs : Vec A n} → ∀{x} → P x      → Any P (x ∷ xs)
  _∷_ : ∀{n} {xs : Vec A n} → ∀ x  → Any P xs → Any P (x ∷ xs)

private
  -- Some lemmae for Any
  hereAny : ∀{A x n} {xs : Vec A n} {P : Pred A} → Any P (x ∷ xs) → ¬(Any P xs) → P x
  hereAny [ Px ]     ¬∃xsP = Px
  hereAny (_ ∷ ∃xsP) ¬∃xsP = ⊥-elim (¬∃xsP ∃xsP)

  laterAny : ∀{A x n} {xs : Vec A n} {P : Pred A} → Any P (x ∷ xs) → ¬(P x) → (Any P xs)
  laterAny [ Px ]     ¬Px = ⊥-elim (¬Px Px)
  laterAny (_ ∷ ∃xsP) ¬Px = ∃xsP

-- Any is decidable for decidable predicates
any : {A : Set} {n : ℕ} {P : Pred A} → (P? : Decidable P) → (xs : Vec A n) → Dec (Any P xs)
any P? [] = no (λ ())
any P? (x ∷ xs) with P? x
...             | yes Px = yes [ Px ]
...             | no ¬Px with any P? xs
...                      | yes ∃xsP = yes (x ∷ ∃xsP)
...                      | no ¬∃xsP = no λ φ → ¬Px (hereAny φ ¬∃xsP)


-- Any can be used to define membership
infix 4 _∈_ _∉_

_∈_ : {A : Set} {n : ℕ} → (x : A) → Vec A n → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} {n : ℕ} → (x : A) → Vec A n → Set
x ∉ xs = ¬(x ∈ xs)

-- Memberhsip is decidable if equality is decidable.
decide∈ : {A : Set} {n : ℕ} → Decidable≡ A → (x : A) → (xs : Vec A n) → Dec (x ∈ xs)
decide∈ _≟_ x xs = any (x ≟_) xs

data Solutions {A B} (P : A → B → Set) : ∀{n} → Vec A n → Vec B n → Set where
  []  : Solutions P [] []
  _∷_ : ∀{x y n} {xs : Vec A n} {ys : Vec B n}
          → P x y → Solutions P xs ys → Solutions P (x ∷ xs) (y ∷ ys)
