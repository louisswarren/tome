We extend the built-in module for lists, by showing that if a predicate over a
type is decidable, then given a list over that type, it is decidable if the
predicate holds on any member, and it is decidable if the predicate holds on
all members.

\AgdaHide{
\begin{code}

module List where

\end{code}
}

First, import the built-in list type. A simplified version of the definition is commented below.
\begin{code}

open import Agda.Builtin.List public

{-
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A
-}

\end{code}
\AgdaHide{
\begin{code}

open import Decidable

\end{code}
}

A list of type $A$ is either empty, or otherwise constructed by prepending an
object of type $A$ to a list of type $A$. Given a predicate $P$ on $A$, the
notion of $P$ holding on every element of a list can be defined in a similar
way.

\begin{code}

data All {A : Set} (P : Pred A) : List A → Set where
  []  : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

\end{code}
In the case that $P$ is decidable, it is also decidable whether $P$ holds on
every element of a list, by simply recursing through and examining $P$ on every
element.
\begin{code}

decAll : ∀{A P} → (p : Decidable P) → (xs : List A) → Dec (All P xs)
decAll p []       = yes []
decAll p (x ∷ xs) with p x
...               | no ¬Px = no λ { (Px ∷ _) → ¬Px Px }
...               | yes Px with decAll p xs
...                        | yes ∀xsP = yes (Px ∷ ∀xsP)
...                        | no ¬∀xsP = no  λ { (_ ∷ ∀xsP) → ¬∀xsP ∀xsP }

\end{code}

For $P$ to hold on \emph{any} element of a list, it must either hold on the
first element, or otherwise in the tail of the list.

\begin{code}

data Any {A : Set} (P : Pred A) : List A → Set where
  [_] : ∀{x xs} → P x → Any P (x ∷ xs)
  _∷_ : ∀{xs} → (x : A) → Any P xs → Any P (x ∷ xs)

\end{code}
Again, the above is decidable for decidable predicates.
\begin{code}

decAny : ∀{A P} → (p : Decidable P) → (xs : List A) → Dec (Any P xs)
decAny p []       = no λ ()
decAny p (x ∷ xs) with p x
...               | yes Px = yes [ Px ]
...               | no ¬Px with decAny p xs
...                        | yes ∃xsP = yes (x ∷ ∃xsP)
...                        | no ¬∃xsP = no  λ { [ Px ]      → ¬Px Px
                                              ; ( _ ∷ ∃xsP) → ¬∃xsP ∃xsP }

\end{code}

We can now define the membership predicate `$\in$' for lists; $x \in xs$ if any
member of $xs$ is equal to $x$. The command \inline{infix} sets the arity of
the infix operators.
\begin{code}

infix 4 _∈_ _∉_

_∈_ : {A : Set} → (x : A) → List A → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → (x : A) → List A → Set
x ∉ xs = ¬(x ∈ xs)

\end{code}
It follows that if equality is decidable, then
membership is decidable.
\begin{code}

dec∈ : ∀{A} → Decidable≡ A → (x : A) → (xs : List A) → Dec (x ∈ xs)
dec∈ _≟_ x xs = decAny (x ≟_) xs

\end{code}
