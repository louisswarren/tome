We begin with a module which defines decidability.

\AgdaHide{
\begin{code}

module Decidable where

\end{code}
}

Agda has a built-in module defining equality. We import this module and
re-export it here. For illustrative purposes, a simplified version of this
definition for small types (types of type \inline{Set}) is commented below.
\begin{code}

open import Agda.Builtin.Equality public

{-
  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x
-}

\end{code}
For every $x$ of any type, there is a constructor for $x \equiv x$. An instance
of the equality $x \equiv y$ is a proof that $x$ and $y$ are intensionally
equal. In Agda, we use \inline{data} types as a convenient notation for what
would otherwise be defined type-theoretically using W-types.

The bottom type, $\bot$, has no constructors, and so is provable only from
absurdity. The usual definition of negation follows, as does an abbreviation for
inequality.
\begin{code}

data ⊥ : Set where

¬_ : (A : Set) → Set
¬ A = A → ⊥

infix 4 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬(x ≡ y)

\end{code}

The principle of \emph{ex falso quodlibet} (EFQ) holds in Agda, in the sense
that any type can be constructed from the bottom type. To show this, we do a
case split on the instance of $\bot$. There is no constructor for $\bot$, which
is stated using empty parentheses. Cases which are not constructable do not
need proving.
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

\end{code}
The constructors \inline{yes} and \inline{no} can be thought of as similar to
the truth values \inline{true} and \inline{false} in the boolean type, with the
addition that they keep the proof or disproof of the proposition for which they
are acting as a truth value.

A unary predicate is \emph{decidable} if each of its values is decidable.
\begin{code}

Pred : Set → Set₁
Pred A = A → Set

Decidable : {A : Set} → Pred A → Set
Decidable P = ∀ x → Dec (P x)

\end{code}
The same could be defined for binary predicates, but this won't be needed.
However, the special case of the equality predicate being decidable for a given
type\footnote{
  This is as much a property of the type as it is a property of the equality
  predicate for that type. A type with a decidable equality is called discrete
  \citep{hasegawa2013typed}. In a programming-focused implementation, we could
  define a type expressing the discreteness of another type, and provide
  \inline{instance} proofs for the discreteness of the types we work with. Agda
  would then find any required decidable equalities implicitly by instance
  resolution. However, in the interests of remaining closer to a type-theoretic
  implementation, we will eschew this Agda feature.}
will be used later.
\begin{code}

Decidable≡ : Set → Set
Decidable≡ A = (x y : A) → Dec (x ≡ y)

\end{code}
Intuitively, inductively defined types which are not constructed from functions
will have a decidable equality, simply by case analysis on the components from
which they are constructed.
