module List where

open import Agda.Builtin.List public

open import Decidable

data All {A : Set} (P : Pred A) : List A → Set where
  []  : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

-- All is decidable for decidable predicates
all : ∀{A} {P : Pred A} → (p : Decidable P) → (xs : List A) → Dec (All P xs)
all p [] = yes []
all p (x ∷ xs) with p x
...            | no ¬Px = no λ { (Px ∷ _) → ¬Px Px }
...            | yes Px with all p xs
...                     | yes ∀xsP = yes (Px ∷ ∀xsP)
...                     | no ¬∀xsP = no λ { (_ ∷ ∀xsP) → ¬∀xsP ∀xsP }


data Any {A : Set} (P : Pred A) : List A → Set where
  [_] : ∀{x xs} → P x → Any P (x ∷ xs)
  _∷_ : ∀{xs} → (x : A) → Any P xs → Any P (x ∷ xs)

-- Any is decidable for decidable predicates
any : ∀{A} {P : Pred A} → (p : Decidable P) → (xs : List A) → Dec (Any P xs)
any p [] = no λ ()
any p (x ∷ xs) with p x
...            | yes Px = yes [ Px ]
...            | no ¬Px with any p xs
...                     | yes ∃xsP = yes (x ∷ ∃xsP)
...                     | no ¬∃xsP = no λ { [ Px ]      → ¬Px Px
                                          ; ( _ ∷ ∃xsP) → ¬∃xsP ∃xsP }


-- Any can be used to define membership
infix 4 _∈_ _∉_

_∈_ : {A : Set} → (x : A) → List A → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → (x : A) → List A → Set
x ∉ xs = ¬(x ∈ xs)

-- Memberhsip is decidable if equality is decidable.
decide∈ : ∀{A} → Decidable≡ A → (x : A) → (xs : List A) → Dec (x ∈ xs)
decide∈ _≟_ x xs = any (x ≟_) xs
