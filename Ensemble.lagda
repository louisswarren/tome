Serious consideration must be given to the data type used to describe the
context of a natural deduction tree. In a proof tree for $\Gamma \vdash
\alpha$, it must be verified that the remaining open assumptions are all
members of $\Gamma$, so the type must have a notion of `subset'. For universal
generalisation introduction, and existential generalisation elimination, it
will also be necessary to verify that a given variable is not free in any open
assumption, so the type must also have a notion for a predicate holding on all
elements. Throughout the natural deduction proof, the collection of open
assumptions is modified, either by making new assumptions, combining
collections of assumptions, or by discharging assumptions. Finally, while we
will giving proofs about natural deduction trees, we would also like to give
proofs regarding actual formulae (and axiom schemes). While doing these, the
focus should be on the structure of the tree, as it would when doing such a
deduction by hand. We would like Agda's proof search to be able to fill in
proof terms regarding variable freedom and open assumptions.

The \inline{List} (or \inline{Vec}) type is not suitable.  While removal of
elements from a list of formulae can be defined with a function, it is unwieldy
to give proofs regarding the results of such computations, as they depend on
equality-checking of formulae, and so proofs must include both the case where
the equality is as expected, and the degenerate case.
\todo{example}

Predicates can be used for this purpose.

\begin{code}

open import Agda.Builtin.Equality

open import Decidable
open import List using (List ; [] ; _∷_)

\end{code}

We define the type \inline{Ensemble}. It is actually another name for
\inline{Pred}, but will be used to refer to predicates which should be thought
of as being created in the manner below. This is only for ease of
understanding, and is not an actual restriction.
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

The ensembles created in the manner below involve negations. While a sensible
definition of subset is $A \subset B \coloneqq \forall x (x \in A \rightarrow x
\in B)$, a proof of this could require EFQ. Inside a lambda expression, this
can be done by use of the lemma \inline{⊥-elim}, but this would have to be
hinted in order for a proof search to find it. For convenience, we adopt a
\todo{minimal} translation by taking the double negative of the right side of
the implication.
\begin{code}
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
have to do a case analysis on a proof of $x \in A \cup B$. As of Agda 2.6.0
\todo{how to cite this?}, Agda's proof search does not support pattern matching
lambda expressions. A definition involving only functions is $x \in A \cup B
\coloneqq x \not\in A \rightarrow x \in B$. We take the double negative of the
right side of the implication.
\begin{code}

infixr 5 _∪_
_∪_ : {A : Set} → Ensemble A → Ensemble A → Ensemble A
(αs ∪ βs) = λ x → x ∉ αs → ¬(x ∉ βs)

\end{code}
Instead of defining a set difference, define notation for removing a single
element from an ensemble. Since we intend to use ensembles only for finite
collections, this is not a limitation. Proofs involving a conjunction (either
by from a cartesian product type or a new data type), expressing that $x \in A
- a$ means $x \in A \text{ and } x \neq A$, would have the same pattern
  matching requirements as disjoint unions. A translation to functions is $x
  \in A - a \coloneqq \lnot(x \in A \rightarrow x = a)$ \todo{Am I using $=$ or
  $\equiv$?}.  Take the contrapositive of the inner implication.
\begin{code}

infixl 5 _-_
_-_ : {A : Set} → Ensemble A → A → Ensemble A
(αs - α) = λ x → ¬(x ≢ α → x ∉ αs)

\end{code}

Of course, ensembles are just predicates, so they can be created in any way
that functions can be created. We can define a type to keep track of the
creation of a predicate, to ensure it was created using (something equal to)
the functions above. Additionally, the type requires that the predicate is over
a type with a decidable equality.
\begin{code}

data Assembled {A : Set} (eq : Decidable≡ A) : Pred A → Set₁ where
  from∅   : Assembled eq ∅
  from⟨_⟩ : (α : A) → Assembled eq (⟨ α ⟩)
  from_∪_ : ∀{αs βs} → Assembled eq αs → Assembled eq βs → Assembled eq (αs ∪ βs)
  from_-_ : ∀{αs} → Assembled eq αs → (α : A) → Assembled eq (αs - α)

\end{code}

Assembled ensembles have decidable membership.
\begin{code}

decide∈ : {A : Set} {eq : Decidable≡ A} {αs : Ensemble A}
          → (x : A) → Assembled eq αs → Dec (x ∈ αs)
\end{code}
Nothing is in the empty ensemble.
\begin{code}
decide∈ x from∅ = no λ x∈∅ → x∈∅
\end{code}
Membership of a singleton is defined by an equality, and so its decidability is
just the the decidable equality from \inline{Assembled}.
\begin{code}
decide∈ {A} {eq} x (from⟨ α ⟩) = eq x α
\end{code}
To check membership for a union, simply check first for membership of the left
ensemble, then the right. The lambda expression proofs given here are
non-trivial, but can be provided by Agda's proof search.
\begin{code}
decide∈ x (from Aαs ∪ Aβs) with decide∈ x Aαs
...   | yes x∈αs = yes λ x∉αs _ → x∉αs x∈αs
...   | no  x∉αs with decide∈ x Aβs
...              | yes x∈βs = yes λ _ x∉βs → x∉βs x∈βs
...              | no  x∉βs = no λ x∉αs∪βs → x∉αs∪βs x∉αs x∉βs
\end{code}
Finally, in the case of an element being removed, use the decidability from
\inline{Assembled} to check if the given element was removed, and otherwise
check if the given element is in the inner ensemble.
\begin{code}
decide∈ {A} {eq} x (from Aαs - α) with eq x α
...   | yes refl = no λ α∈αs-α → α∈αs-α λ α≢α _ → α≢α refl
...   | no x≢α   with decide∈ x Aαs
...              | yes x∈αs = yes λ x≢α→x∉αs → x≢α→x∉αs x≢α x∈αs
...              | no  x∉αs = no  λ x∈αs-α
                                    → x∈αs-α (λ _ _
                                              → x∈αs-α (λ _ _
                                                        → x∈αs-α (λ _ → x∉αs)))

\end{code}

We define what it means for a property $P$ to hold on every member of an
ensemble $\alpha s$. We recurse through the ensemble, forking at unions. When
reaching a removal, the removed element is added to a list which accumulates
removed elements. For each element, we require either that $P$ holds for the
element, or else that it is in the list of removed elements.  Finally, $P$
holds on all of $\alpha s$ if it holds according to the above procedure, with
the removed element list starting empty.
\todo{Explain, motivation}

\begin{code}

infixr 5 _all∪_

data All_[_∖_] {A : Set} (P : Pred A) : Ensemble A → List A → Set₁ where
  all∅    : ∀{xs}       → All P [ ∅ ∖ xs ]
  all⟨_⟩  : ∀{xs α}     → P α         → All P [ ⟨ α ⟩ ∖ xs ]
  all⟨-_⟩ : ∀{xs α}     → α List.∈ xs → All P [ ⟨ α ⟩ ∖ xs ]
  _all∪_  : ∀{αs βs xs} → All P [ αs ∖ xs ] → All P [ βs ∖ xs ]
                          → All P [ αs ∪ βs ∖ xs ]
  all-_   : ∀{αs x xs}  → All P [ αs ∖ x ∷ xs ] → All P [ αs - x ∖ xs ]

All : {A : Set} → Pred A → Ensemble A → Set₁
All P αs = All P [ αs ∖ [] ]

FAll→All : {A : Set} {eq : Decidable≡ A} {P : Pred A} {αs : Ensemble A}
            → Assembled eq αs → (∀ x → x ∈ αs → P x) → All P αs
FAll→All {A} {eq} {P} Aαs fall = φ Aαs [] (λ x x∈αs _ → fall x x∈αs)
  where
    φ : ∀{αs} → Assembled eq αs → ∀ xs → (∀ x → x ∈ αs → x List.∉ xs → P x)
        → All P [ αs ∖ xs ]
    φ from∅            xs fall = all∅
    φ from⟨ α ⟩        xs fall with List.decide∈ eq α xs
    ...                    | yes α∈xs = all⟨- α∈xs ⟩
    ...                    | no  α∉xs = all⟨ fall α refl α∉xs ⟩
    φ (from Aαs ∪ Aβs) xs fall = (φ Aαs xs fallαs) all∪ (φ Aβs xs fallβs)
      where
        fallαs : _
        fallαs x x∈αs = fall x (λ x∉αs _    → x∉αs x∈αs)
        fallβs : _
        fallβs x x∈βs = fall x (λ _    x∉βs → x∉βs x∈βs)
    φ (from Aαs - α)   xs fall = all- (φ Aαs (α ∷ xs) fallαs-α)
      where
        fallαs-α : _
        fallαs-α x x∈αs x∉α∷xs =
          let x∈αs-α : _
              x∈αs-α x≢α→x∉αs = x≢α→x∉αs (λ x≢α → x∉α∷xs List.[ x≢α ]) x∈αs
              x∉xs   : x List.∉ xs
              x∉xs   x∈xs = x∉α∷xs (α ∷ x∈xs)
          in  fall x x∈αs-α x∉xs
\end{code}
