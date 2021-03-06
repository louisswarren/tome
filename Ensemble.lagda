Serious consideration must be given to the data type used to describe the
context of a natural deduction tree. In a proof tree for $\Gamma \vdash
\alpha$, it must be verified that the remaining open assumptions are all
members of $\Gamma$, so the type must have a notion of `subset'. For universal
generalisation introduction, and existential generalisation elimination, it
will also be necessary to verify that a given variable is not free in any open
assumption, so the type must also have a notion for a predicate holding on all
elements. Throughout the natural deduction proof, the collection of open
assumptions is modified, either by making new assumptions, by combining
collections of assumptions, or by discharging assumptions. Finally, while we
will be giving proofs about natural deduction trees, we would also like to give
proofs regarding actual formulae (and axiom schemes). Giving natural deduction
proofs in this system should correspond closely to doing natural deduction
(from the bottom up) by hand. There should not be any need for operations other
than the usual rules for natural deduction (with a single exception at the
beginning of the proof, as will be shown later). Any manipulation of the
context should be done automatically by Agda, and proofs regarding variable
freedom and open assumptions should be solvable using Agda's proof search.

The \inline{List} (or \inline{Vec}) type is not suitable. While removal of
elements from a list of formulae can be defined with a function, it is unwieldy
to give proofs regarding the results of such computations, as they depend on
equality-checking of formulae, and so proofs must include both the case where
the equality is as expected, and the degenerate case.\footnote{Examples of this
are included in the appendix.}

An implementation of classical propositional logic in the style of natural
deduction was given in \citet{caiproplogicagda2015}. While this does use
(something equivalent to) lists, it requires frequent use of extra deduction
rules for weakening the context. This would not be suitable for a natural
deduction assistant, and it also does not solve the problems given above for
first order logic.

\AgdaHide{
\begin{code}

module Ensemble where

open import Decidable
open import List using (List ; [] ; _∷_)

\end{code}
}

Predicates can be used to store collections of values, in the manner of set
comprehension.  We define the type \inline{Ensemble} as another name for
\inline{Pred}. It will be used to refer to predicates which have been created
in a manner to follow. This is only for ease of understanding, and is not an
actual restriction. Ensembles will resemble finite sets.
\begin{code}

Ensemble : Set → Set₁
Ensemble A = A → Set

\end{code}
Membership is defined by satisfying the predicate.
\begin{code}

infix 4 _∈_ _∉_

_∈_ : {A : Set} → A → Ensemble A → Set
α ∈ αs = αs α

_∉_ : {A : Set} → A → Ensemble A → Set
α ∉ αs = ¬(α ∈ αs)

\end{code}

A sensible definition of subset is $A \subset B$ if $\forall x (x \in A
\rightarrow x \in B)$. However, some ensembles will be defined using negations.
If it is absurd for $x$ to be in $A$ (for example, if $A$ is the empty set),
then proving that $x \in B$ can be done by either pattern matching to an empty
case, or using the lemma \inline{⊥-elim}. However, Agda's proof search will not
do pattern matching inside lambda
expressions,\footnote{
  As of version 2.6.0.}
and it will not find lemmas unless it is hinted to do so. For convenience, we
adopt a minimal logic translation by taking the double negative of the right
side of the implication, which solves this issue.\footnote{
  A catalogue of negative translations can be found in
  \citet{oliviatranslations}. The translation we use is less complete, as we
  use only enough negations to make the subset predicate minimally provable.}
\begin{code}

infix 4 _⊂_
_⊂_ : {A : Set} → Ensemble A → Ensemble A → Set
αs ⊂ βs = ∀ x → x ∈ αs → ¬(x ∉ βs)

\end{code}

The empty ensemble and singleton ensembles are defined in the obvious way.
\begin{code}

∅ : {A : Set} → Ensemble A
∅ = λ _ → ⊥

⟨_⟩ : {A : Set} → A → Ensemble A
⟨ α ⟩ = λ x → x ≡ α

\end{code}
It would be reasonable to define union in terms of a disjoint union type, so
that a proof of $x \in A \cup B$ would be either a proof of $x \in A$ or of $x
\in B$. However, we want Agda's proof search to fill in proofs regarding
subsets. For a proof that $A \cup B \subset A \cup B \cup \emptyset$, we would
have to do a case analysis on a proof of $x \in A \cup B$. Instead we define $x
\in A \cup B$ using functions, so that pattern matching is not necessary in
order to make use of such a proof. One definition involving only functions is
$x \in A \cup B \coloneqq x \not\in A \rightarrow x \in B$. We take the double
negative of the right side of the implication, for the same reasons as above.
\begin{code}

infixr 5 _∪_
_∪_ : {A : Set} → Ensemble A → Ensemble A → Ensemble A
(αs ∪ βs) = λ x → x ∉ αs → ¬(x ∉ βs)

\end{code}
Instead of defining a set difference, we define notation for removing a single
element from an ensemble. Since ensembles will be used only for finite
collections, this is not a limitation. A definition using conjunctions is that
$x \in A - a$ means $x \in A \text{ and } x \neq a$. Translating this to
functions gives $x \in A - a \coloneqq \lnot(x \in A \rightarrow x \equiv a)$.
Take the contrapositive of the inner implication.
\begin{code}

infixl 5 _-_
_-_ : {A : Set} → Ensemble A → A → Ensemble A
(αs - α) = λ x → ¬(x ≢ α → x ∉ αs)

\end{code}
These definitions allow subset propositions to be proved without case analysis
or \inline{⊥-elim} (EFQ), by adopting functional definitions and using double
negations. Moreover, the only quantifier used in the definitions is in the
definition of \inline{_⊂_}. Since functions are equivalent to implications, we
have translated the notion of subset to a proposition of the form $\forall x
A$, where $A$ is a formula in the implicational fragment of minimal logic. This
is to be expected, since we wanted the proof terms to be simply typed lambda
calculus terms, which is precisely equivalent to minimal logic
\citep{curryhoward}.

Subset proofs can now be solved by Agda automatically, with good performance.
In the case of all natural deduction proofs to follow, Agda solved the subset
proof in less than one second (the default time limit for proof search).
Moreover, since the implicational fragment of minimal logic is decidable, there
are proof search algorithms which will always find a proof if one exists
\citep{weich2001}.

Of course, ensembles are just predicates, so they can be created in any way
that functions can be created. We can define a type to keep track of the
creation of a predicate, to ensure it was created using (something equal to)
the functions above. Additionally, the type requires that the predicate is over
a type with a decidable equality.
\begin{code}

data Assembled {A : Set} (eq : Decidable≡ A) : Pred A → Set₁ where
  from∅   : Assembled eq ∅
  from⟨_⟩ : (α : A)  → Assembled eq (⟨ α ⟩)
  from_∪_ : ∀{αs βs} → Assembled eq αs → Assembled eq βs
                       → Assembled eq (αs ∪ βs)
  from_-_ : ∀{αs}    → Assembled eq αs → (α : A) → Assembled eq (αs - α)

\end{code}

\begin{proposition}
Assembled ensembles have decidable membership.
\end{proposition}
\begin{proof}
$ $
\begin{code}

dec∈ : {A : Set} {eq : Decidable≡ A} {αs : Ensemble A}
       → (x : A) → Assembled eq αs → Dec (x ∈ αs)
\end{code}
Nothing is in the empty ensemble.
\begin{code}
dec∈          x from∅            = no λ x∈∅ → x∈∅
\end{code}
Membership of a singleton is defined by an equality, and so its decidability is
just the the decidable equality from \inline{Assembled}.
\begin{code}
dec∈ {_} {eq} x (from⟨ α ⟩)      = eq x α
\end{code}
To check membership for a union, simply check first for membership of the left
ensemble, then the right. The lambda expression proofs given here are
non-trivial, and difficult to interpret, but can be provided by Agda's proof
search.
\begin{code}
dec∈          x (from Aαs ∪ Aβs) with dec∈ x Aαs
...   | yes x∈αs = yes λ x∉αs _ → x∉αs x∈αs
...   | no  x∉αs with dec∈ x Aβs
...              | yes x∈βs = yes λ _ x∉βs → x∉βs x∈βs
...              | no  x∉βs = no  λ x∉αs∪βs → x∉αs∪βs x∉αs x∉βs
\end{code}
Finally, in the case of an element being removed, use the decidable equality
from \inline{Assembled} to check if the given element was removed, and
otherwise check if the given element is in the inner ensemble.
\begin{code}
dec∈ {_} {eq} x (from Aαs - α)   with eq x α
...   | yes refl = no λ α∈αs-α → α∈αs-α λ α≢α _ → α≢α refl
...   | no x≢α   with dec∈ x Aαs
...              | yes x∈αs = yes λ x≢α→x∉αs → x≢α→x∉αs x≢α x∈αs
...              | no  x∉αs = no  λ x∈αs-α
                                    → x∈αs-α (λ _ _
                                              → x∈αs-α (λ _ _
                                                        → x∈αs-α (λ _
                                                                  → x∉αs)))

\end{code}
\codeqed
\end{proof}

Given an ensemble $A$, a sensible definition for a predicate $P$ holding on
every element of $A$ would be $\forall x (x \in A \rightarrow P x)$. However,
for inductively defined predicates (like \inline{_notFreeIn α} for some
$\alpha$), this is not easy to work with, either by hand or using proof search.
For example, to prove that the variable $y$ is not free in all members of
$\{\forall y Q y\}\cup\{\bot\}$, it would be necessary to show that every
member is equal to either $\forall y Q y$ or $\bot$, and only then supply the
required constructors for each case. Once again, this requires pattern
matching.

Instead, for an assembled ensemble, we give a definition for \inline{All} which
utilises the structure of the ensemble, and describes what computation must be
performed to check that a predicate holds on all members. To do so, maintain a
list of all elements which have been removed from the ensemble.
\begin{code}

infixr 5 _all∪_

data All_[_∖_] {A : Set} (P : Pred A) : Ensemble A → List A → Set₁ where
  all∅    : ∀{xs}       → All P [ ∅ ∖ xs ]
\end{code}
$P$ holds on all of a singleton if it holds on the element of the singleton, or
else if that element has already been removed.
\begin{code}
  all⟨_⟩  : ∀{α xs}     → P α         → All P [ ⟨ α ⟩ ∖ xs ]
  all⟨-_⟩ : ∀{α xs}     → α List.∈ xs → All P [ ⟨ α ⟩ ∖ xs ]
\end{code}
In the case of a union, $P$ must hold on both sides of the union.
\begin{code}
  _all∪_  : ∀{αs βs xs} → All P [ αs ∖ xs ] → All P [ βs ∖ xs ]
                          → All P [ αs ∪ βs ∖ xs ]
\end{code}
Finally, when an ensemble has been created by removing an element from another,
check that $P$ holds on the other ensemble for all values other than the
removed one.
\begin{code}
  all-_   : ∀{αs x xs}  → All P [ αs ∖ x ∷ xs ] → All P [ αs - x ∖ xs ]

\end{code}

Now, $P$ holds on all of $\alpha s$ if it holds according to the above
procedure, with the removed element list starting empty.
\begin{code}

All : {A : Set} → Pred A → Ensemble A → Set₁
All P αs = All P [ αs ∖ [] ]

\end{code}

\begin{proposition}
The definition of \inline{All} for assembled ensembles is weaker than the usual
set definition.
\end{proposition}
\begin{proof}
We use a lemma to show that this is the case for all values of the removed list
of elements, and apply it to the case of the empty list.
\begin{code}

fAll→All : {A : Set} {eq : Decidable≡ A} {P : Pred A} {αs : Ensemble A}
            → Assembled eq αs → (∀ x → x ∈ αs → P x) → All P αs
fAll→All {A} {eq} {P} Aαs fall = φ Aαs [] (λ x x∈αs _ → fall x x∈αs)
  where
    φ : ∀{αs} → Assembled eq αs → ∀ xs
                → (∀ x → x ∈ αs → x List.∉ xs → P x) → All P [ αs ∖ xs ]
    φ from∅            xs fall∅     = all∅
\end{code}
For a singleton $\{\alpha\}$, either $\alpha$ has been removed, or otherwise it
has not been removed, in which case we use the functional all to prove $P
\alpha$.
\begin{code}
    φ from⟨ α ⟩        xs fall⟨α⟩   with List.dec∈ eq α xs
    ...                             | yes α∈xs = all⟨- α∈xs ⟩
    ...                             | no  α∉xs = all⟨ fall⟨α⟩ α refl α∉xs ⟩
\end{code}
Since unions are defined using a double negation, to show that the functional
all for a union means functional all for each of the two ensembles, use a
contradiction for each.
\begin{code}
    φ (from Aαs ∪ Aβs) xs fallαs∪βs = (φ Aαs xs fallαs)
                                      all∪ (φ Aβs xs fallβs)
      where
        fallαs : _
        fallαs x x∈αs = fallαs∪βs x (λ x∉αs _    → x∉αs x∈αs)
        fallβs : _
        fallβs x x∈βs = fallαs∪βs x (λ _    x∉βs → x∉βs x∈βs)
\end{code}
In the case of $\alpha s - \alpha$, we show first that if $x \in \alpha s$ then
$x \in \alpha s - \alpha$, and that if $x \not\in \alpha \Colon xs$ then $x
\not\in xs$.
\begin{code}
    φ (from Aαs - α)   xs fallαs-α  = all- (φ Aαs (α ∷ xs) fallαs)
      where
        fallαs : _
        fallαs x x∈αs x∉α∷xs =
          let x∈αs-α : _
              x∈αs-α x≢α→x∉αs = x≢α→x∉αs (λ x≢α → x∉α∷xs List.[ x≢α ]) x∈αs
              x∉xs   : x List.∉ xs
              x∉xs   x∈xs = x∉α∷xs (α ∷ x∈xs)
          in  fallαs-α x x∈αs-α x∉xs
\end{code}
\codeqed
\end{proof}

The converse cannot be proved; \inline{All} is in fact strictly weaker than the
functional definition. While it could be expected that pattern matching on both
\inline{All} and \inline{Assembled} would lead to a proof, this will not work
because Agda cannot unify function types. For example, in the case that an
ensemble was assembled by \inline{from Aαs ∪ Aβs}, case analysis of the proof
of \inline{All P (αs ∪ βs)} does not show that the only constructor is
\inline{_all∪_}; Agda cannot determine that \inline{λ x → x ∉ αs → ¬(x ∉ βs)}
does not unify with \inline{λ _ → ⊥}, so \inline{all∅} may or may not be a
constructor.  If we wanted a stronger type which is equivalent to the
functional definition, the assembled structure would need to be included in
\inline{All}.

We can use the \inline{All} predicate to define the restriction that certain
deductions are valid only if a given variable is not free in an ensemble of
open assumptions.  For the usual use case (i.e. cases other than abstract proof
tree manipulation where variable freedom is determined by some lemma), Agda's
proof search will find the required proof. However, due to the above
limitations with unification of functions, Agda does not see that there is only
one constructor for each non-singleton ensemble, so the search algorithm is not
fast. For larger proof trees, it is necessary to increase the timeout from the
default one second to ten seconds. This could also be resolved by including the
assembled structure in \inline{All}.
