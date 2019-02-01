\section{Decidable.lagda}

\begin{code}

module Decidable where

open import Agda.Builtin.Equality public

data ⊥ : Set where

¬_ : (A : Set) → Set
¬ A = A → ⊥

\end{code}

EFQ holds in Agda.

\begin{code}

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬(x ≡ y)

\end{code}

A proposition (type) is decidable if it can be proved (constructed), or
otherwise if its proof (construction) leads to a proof (construction) of
$\bot$.

\begin{code}

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

Pred : Set → Set₁
Pred A = A → Set

Decidable : {A : Set} → Pred A → Set
Decidable P = ∀ x → Dec (P x)

Decidable≡ : Set → Set
Decidable≡ A = (x y : A) → Dec (x ≡ y)

\end{code}
