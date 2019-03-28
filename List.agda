Lists are finite objects. If a property over a type is decidable, then it is
decidable whether that property holds for any or all members of a list of that
type.

\begin{code}

module List where

open import Agda.Builtin.List public

open import Decidable

\end{code}

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

The membership predicate `$\in$' can be defined in terms of $\mathrm{Any}$; $x
\in xs$ if any member of $xs$ is equal to $x$. It follows that if equality is
decidable, then membership is decidable.

The command \inline{infix} sets the arity of the infix operators.

\begin{code}

infix 4 _∈_ _∉_

_∈_ : {A : Set} → (x : A) → List A → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → (x : A) → List A → Set
x ∉ xs = ¬(x ∈ xs)

decide∈ : ∀{A} → Decidable≡ A → (x : A) → (xs : List A) → Dec (x ∈ xs)
decide∈ _≟_ x xs = any (x ≟_) xs

\end{code}
