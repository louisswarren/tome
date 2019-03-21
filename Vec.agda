module Vec where

open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Decidable

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)


data All {A : Set} (P : Pred A) : ∀{n} → Vec A n → Set where
  []  : All P []
  _∷_ : ∀{x n} {xs : Vec A n} → P x → All P xs → All P (x ∷ xs)

-- All is decidable for decidable predicates
all : ∀{A n} {P : Pred A} → (p : Decidable P) → (xs : Vec A n) → Dec (All P xs)
all p [] = yes []
all p (x ∷ xs) with p x
...            | no ¬Px = no λ { (Px ∷ _) → ¬Px Px }
...            | yes Px with all p xs
...                     | yes ∀xsP = yes (Px ∷ ∀xsP)
...                     | no ¬∀xsP = no λ { (_ ∷ ∀xsP) → ¬∀xsP ∀xsP }


data Any {A : Set} (P : Pred A) : ∀{n} → Vec A n → Set where
  [_] : ∀{n x} {xs : Vec A n}       → P x      → Any P (x ∷ xs)
  _∷_ : ∀{n}   {xs : Vec A n} → ∀ x → Any P xs → Any P (x ∷ xs)

-- Any is decidable for decidable predicates
any : ∀{A n} {P : Pred A} → (p : Decidable P) → (xs : Vec A n) → Dec (Any P xs)
any p [] = no λ ()
any p (x ∷ xs) with p x
...            | yes Px = yes [ Px ]
...            | no ¬Px with any p xs
...                     | yes ∃xsP = yes (x ∷ ∃xsP)
...                     | no ¬∃xsP = no λ { [ Px ]      → ¬Px Px
                                          ; ( _ ∷ ∃xsP) → ¬∃xsP ∃xsP }


-- Any can be used to define membership
infix 4 _∈_ _∉_

_∈_ : {A : Set} {n : ℕ} → (x : A) → Vec A n → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} {n : ℕ} → (x : A) → Vec A n → Set
x ∉ xs = ¬(x ∈ xs)

-- Memberhsip is decidable if equality is decidable.
decide∈ : ∀{A n} → Decidable≡ A → (x : A) → (xs : Vec A n) → Dec (x ∈ xs)
decide∈ _≟_ x xs = any (x ≟_) xs
