\begin{code}

module Decidable where

open import Agda.Builtin.Equality public

\end{code}

For every $x$ of any type, there is a constructor for $x \equiv x$. An instance
of the equality $x \equiv y$ is a proof that $x$ and $y$ are intensionally
equal.

The bottom type, $\bot$, has no constructors, and so is provable only from
absurdity.

\begin{code}

data ⊥ : Set where

¬_ : (A : Set) → Set
¬ A = A → ⊥

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬(x ≡ y)

\end{code}

EFQ holds in Agda. To show this, we do a case split on the instance of $\bot$.
There is no constructor for $\bot$, which Agda shows with empty parentheses.
Cases which are not constructable do not need proving.

\begin{code}

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

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
