Lists are finite objects. If a property over a type is decidable, then it is
decidable whether that property holds for any or all members of a list of that
type.

\begin{code}

module List where

open import Agda.Builtin.List public

open import Decidable

data All {A : Set} (P : Pred A) : List A → Set where
  []  : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

all : ∀{A} {P : Pred A} → (p : Decidable P) → (xs : List A) → Dec (All P xs)
all p [] = yes []
all p (x ∷ xs) with p x
...            | no ¬Px = no ¬all
                          where
                            ¬all : ¬(All _ (x ∷ xs))
                            ¬all (Px ∷ _) = ¬Px Px
...            | yes Px with all p xs
...                     | yes ∀xsP = yes (Px ∷ ∀xsP)
...                     | no ¬∀xsP = no ¬all
                                     where
                                       ¬all : ¬(All _ (x ∷ xs))
                                       ¬all (_ ∷ ∀xsP) = ¬∀xsP ∀xsP


data Any {A : Set} (P : Pred A) : List A → Set where
  [_] : ∀{x xs} → P x → Any P (x ∷ xs)
  _∷_ : ∀{xs} → (x : A) → Any P xs → Any P (x ∷ xs)

any : ∀{A} {P : Pred A} → (p : Decidable P) → (xs : List A) → Dec (Any P xs)
any p [] = no λ ()
any p (x ∷ xs) with p x
...            | yes Px = yes [ Px ]
...            | no ¬Px with any p xs
...                     | yes ∃xsP = yes (x ∷ ∃xsP)
...                     | no ¬∃xsP = no ¬any
                                     where
                                       ¬any : ¬(Any _ (x ∷ xs))
                                       ¬any [ Px ] = ¬Px Px
                                       ¬any ( _ ∷ ∃xsP) = ¬∃xsP ∃xsP

\end{code}

In particular, if equality is decidable, then membership is decidable.

\begin{code}

infix 4 _∈_ _∉_

_∈_ : {A : Set} → (x : A) → List A → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → (x : A) → List A → Set
x ∉ xs = ¬(x ∈ xs)

decide∈ : ∀{A} → Decidable≡ A → (x : A) → (xs : List A) → Dec (x ∈ xs)
decide∈ _≟_ x xs = any (x ≟_) xs

\end{code}
