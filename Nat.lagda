There is a built-in module for natural numbers, which defines the arithmetic
operations and boolean relations, including a boolean-valued equality. We
import and augment this with some propositions and predicates. The
(unicode-renamed) definition of natural numbers is commented below.

\AgdaHide{
\begin{code}

module Nat where

\end{code}
}
\begin{code}

open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_<_) public

{-
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ
-}

\end{code}
\AgdaHide{
\begin{code}

open import Decidable

\end{code}
}

The built-in boolean-valued equality \inline{_==_} can be evaluated to check
that \inline{1 + 1 == 2} is \inline{true}. However, this is not useful as a
lemma. Instead, we would like to have a binary predicate for natural numbers
which gives either a proof of equality or a proof of inequality. Such a
predicate is itself a proof that equality of natural numbers is decidable,
given the definition of \inline{Decidable≡} above.

The proof is by case analysis on the arguments. In the case where both numbers
are zero, they can be proven equal simply by \inline{refl}. Where only one
number is a successor, they can be proven not equal by doing case analysis on
what their equality would be. As the only constructor for \inline{_≡_} requires
that the left and right sides are the same, and \inline{zero} cannot be unified
with \inline{suc _}, the cases are empty. Finally, if both numbers are
successors, check if their predecessors are equal. If so, then equality
follows. Otherwise, assuming the numbers are equal leads to a contradiction.
\begin{code}

natEq : Decidable≡ ℕ
natEq zero    zero    = yes refl
natEq zero    (suc m) = no λ ()
natEq (suc n) zero    = no λ ()
natEq (suc n) (suc m) with natEq n m
...                   | yes refl = yes refl
...                   | no  n≢m  = no  λ { refl → n≢m refl }

\end{code}

A propositional order relation on the natural numbers can be defined as usual.
\begin{code}

data _≤_ : ℕ → ℕ → Set where
  0≤n   : ∀{n} → zero ≤ n
  sn≤sm : ∀{n m} → n ≤ m → suc n ≤ suc m

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

\end{code}
In the definition of `$\leq$', the type is \emph{indexed} by a pair of natural
numbers, rather than parametrised (given specific names, on the left side of
the colon). This is an example of a dependent type. The constructors do not
produce values of the same type. Moreover, there are types for which there is no
constructor. For example, there is no way of constructing \inline{1 ≤ 0}. In
this manner, dependent types can describe predicates.

The relation \inline{_≤_} is reflexive and transitive.
\begin{code}

≤refl : ∀{n} → n ≤ n
≤refl {zero}  = 0≤n
≤refl {suc n} = sn≤sm ≤refl

≤trans : ∀{x y z} → x ≤ y → y ≤ z → x ≤ z
≤trans 0≤n         y≤z         = 0≤n
≤trans (sn≤sm x≤y) (sn≤sm y≤z) = sn≤sm (≤trans x≤y y≤z)

\end{code}

If $n < m$ then $m \not\leq n$, and if $m \leq n$ then $n \not< m$. This can be
expressed as a single proposition. To derive $\bot$, recurse on $n$ and $m$
until one of them is $0$, at which point there is either no constructor for $n
< m$ or no constructor for $m \leq n$. \todo{rename this}
\begin{code}

ℕdisorder : ∀{n m} → n < m → m ≤ n → ⊥
ℕdisorder (sn≤sm n<m) (sn≤sm m≤n) = ℕdisorder n<m m≤n

\end{code}

Given natural numbers $n$ and $m$, it is possible to compute whether $n \leq m$
or $m \leq n$. To prove this, we first create a proposition \inline{Compare n m}
which is constructed by a proof of either of these.
\begin{code}

data Compare (n m : ℕ) : Set where
  less : n ≤ m → Compare n m
  more : m ≤ n → Compare n m

\end{code}
It remains to show that given any $n$ and $m$, we may construct
\inline{Compare n m}.
\begin{code}

compare : ∀ n m → Compare n m
compare zero    m       = less 0≤n
compare (suc n) zero    = more 0≤n
compare (suc n) (suc m) with compare n m
...                     | less n≤m = less (sn≤sm n≤m)
...                     | more m≤n = more (sn≤sm m≤n)

\end{code}
While it is possible to directly define a function which returns the greater of
two natural numbers, this method preserves the proof showing which is greater.
Defining a relation, and then supplying a function to construct it from all
possible arguments is a common technique, and it will be used often.
