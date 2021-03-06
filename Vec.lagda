Vectors are similar to lists, but the type is indexed by length. For example,
vectors in $\mathbb{N}^2$ are of different type to vectors in $\mathbb{N}^3$.

\AgdaHide{
\begin{code}

module Vec where

open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Decidable

\end{code}
}
\begin{code}

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

\end{code}

We define All, Any, and membership the same was as for lists. The decidability
proofs below are omitted, as they are identical to the corresponding proofs for
lists.

\begin{code}

data All {A : Set} (P : Pred A) : ∀{n} → Vec A n → Set where
  []  : All P []
  _∷_ : ∀{x n} {xs : Vec A n} → P x → All P xs → All P (x ∷ xs)

decAll : ∀{A n P} → (p : Decidable P) → (xs : Vec A n) → Dec (All P xs)
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

decAll p []       = yes []
decAll p (x ∷ xs) with p x
...               | no ¬Px = no λ { (Px ∷ _) → ¬Px Px }
...               | yes Px with decAll p xs
...                        | yes ∀xsP = yes (Px ∷ ∀xsP)
...                        | no ¬∀xsP = no λ { (_ ∷ ∀xsP) → ¬∀xsP ∀xsP }

\end{code}
}
\begin{code}

data Any {A : Set} (P : Pred A) : ∀{n} → Vec A n → Set where
  [_] : ∀{n x} {xs : Vec A n} → P x → Any P (x ∷ xs)
  _∷_ : ∀{n}   {xs : Vec A n} → (x : A) → Any P xs → Any P (x ∷ xs)

decAny : ∀{A n P} → (p : Decidable P) → (xs : Vec A n) → Dec (Any P xs)
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

decAny p []       = no λ ()
decAny p (x ∷ xs) with p x
...               | yes Px = yes [ Px ]
...               | no ¬Px with decAny p xs
...                        | yes ∃xsP = yes (x ∷ ∃xsP)
...                        | no ¬∃xsP = no  λ { [ Px ]      → ¬Px Px
                                              ; ( _ ∷ ∃xsP) → ¬∃xsP ∃xsP }

\end{code}
}
\begin{code}

infix 4 _∈_ _∉_

_∈_ : {A : Set} {n : ℕ} → (x : A) → Vec A n → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} {n : ℕ} → (x : A) → Vec A n → Set
x ∉ xs = ¬(x ∈ xs)

dec∈ : ∀{A n} → Decidable≡ A → (x : A) → (xs : Vec A n) → Dec (x ∈ xs)
dec∈ _≟_ x xs = decAny (x ≟_) xs

\end{code}
