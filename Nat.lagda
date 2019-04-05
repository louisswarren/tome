\begin{code}

module Nat where

open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_<_) public

open import Decidable

\end{code}

Equality of natural numbers is decidable.
\todo{Explain}

\begin{code}

natEq : Decidable≡ ℕ
natEq zero zero = yes refl
natEq zero (suc m) = no λ ()
natEq (suc n) zero = no λ ()
natEq (suc n) (suc m) with natEq n m
...                   | yes refl = yes refl
...                   | no  n≢m  = no λ { refl → n≢m refl }

\end{code}

We augment the built-in definition of the natural numbers with a propositional
ordering.

\begin{code}

data _≤_ : ℕ → ℕ → Set where
  0≤n   : ∀{n} → zero ≤ n
  sn≤sm : ∀{n m} → n ≤ m → suc n ≤ suc m

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

\end{code}

Some lemata which will be useful later:

\begin{code}

¬<refl : ∀{n} → ¬(n < n)
¬<refl {zero}  ()
¬<refl {suc n} (sn≤sm x) = ¬<refl x

≤refl : ∀{n} → n ≤ n
≤refl {zero}  = 0≤n
≤refl {suc n} = sn≤sm ≤refl

≤trans : ∀{x y z} → x ≤ y → y ≤ z → x ≤ z
≤trans 0≤n         y≤z         = 0≤n
≤trans (sn≤sm x≤y) (sn≤sm y≤z) = sn≤sm (≤trans x≤y y≤z)

\end{code}

Given natural numbers $n$ and $m$, it is possible to compute whether $n \leq m$
or $m \leq n$. To prove this, we first create a proposition $\mathrm{Max}\, n\, m$
which is constructed by a proof of either of these.  It then remains to show
that given any $n$ and $m$, we may construct $\mathrm{Max}\, n\, m$.

\begin{code}

data Max (n m : ℕ) : Set where
  less : n ≤ m → Max n m
  more : m ≤ n → Max n m

max : ∀ n m → Max n m
max zero    m       = less 0≤n
max (suc n) zero    = more 0≤n
max (suc n) (suc m) with max n m
max (suc n) (suc m) | less n≤m = less (sn≤sm n≤m)
max (suc n) (suc m) | more m≤n = more (sn≤sm m≤n)

\end{code}

While it is possible to directly define a function which returns the greater of
two natural numbers, this method preserves the proposition showing which is
greater. This is a common technique, and it will be used often.
