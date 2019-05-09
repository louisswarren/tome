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



\begin{code}

Ensemble : Set → Set₁
Ensemble A = A → Set

infix 4 _∈_ _∉_

_∈_ : {A : Set} → A → Ensemble A → Set
α ∈ αs = αs α

_∉_ : {A : Set} → A → Ensemble A → Set
α ∉ αs = ¬(α ∈ αs)

\end{code}



\begin{code}

infixr 5 _∪_
infixl 5 _-_

∅ : {A : Set} → Ensemble A
∅ _ = ⊥

⟨_⟩ : {A : Set} → A → Ensemble A
⟨ α ⟩ x = x ≡ α

_-_ : {A : Set} → Ensemble A → A → Ensemble A
(αs - α) x = ¬(x ≢ α → x ∉ αs)

_∪_ : {A : Set} → Ensemble A → Ensemble A → Ensemble A
(αs ∪ βs) x = x ∉ αs → ¬(x ∉ βs)

\end{code}



\begin{code}

data Assembled {A : Set} (eq : Decidable≡ A) : Pred A → Set₁ where
  from∅   : Assembled eq ∅
  from⟨_⟩ : (α : A) → Assembled eq (⟨ α ⟩)
  from_-_ : ∀{αs} → Assembled eq αs → (α : A) → Assembled eq (αs - α)
  from_∪_ : ∀{αs βs} → Assembled eq αs → Assembled eq βs → Assembled eq (αs ∪ βs)

\end{code}



\begin{code}

decide∈ : {A : Set} {eq : Decidable≡ A} {αs : Ensemble A}
          → (x : A) → Assembled eq αs → Dec (x ∈ αs)
decide∈ x from∅ = no λ x∈∅ → x∈∅
decide∈ {A} {eq} x (from⟨ α ⟩) with eq x α
...                            | yes refl = yes refl
...                            | no x≢α   = eq x α
decide∈ {A} {eq} x (from Aαs - α) with eq x α
...                               | yes refl = no λ α∈αs-α → α∈αs-α λ α≢α _ → α≢α refl
...                               | no x≢α   with decide∈ x Aαs
...                                          | yes x∈αs = yes λ x≢α→x∉αs → x≢α→x∉αs x≢α x∈αs
...                                          | no  x∉αs = no  λ x∈αs-α → x∈αs-α λ _ _ → x∈αs-α λ _ _ → x∈αs-α (λ _ → x∉αs)
decide∈ x (from Aαs ∪ Aβs) with decide∈ x Aαs
...                        | yes x∈αs = yes λ x∉αs _ → x∉αs x∈αs
...                        | no  x∉αs with decide∈ x Aβs
...                                   | yes x∈βs = yes λ _ x∉βs → x∉βs x∈βs
...                                   | no  x∉βs = no λ x∉αs∪βs → x∉αs∪βs x∉αs x∉βs

\end{code}



\begin{code}

_⊂_ : {A : Set} → Ensemble A → Ensemble A → Set
αs ⊂ βs = ∀ x → x ∈ αs → ¬(x ∉ βs)

\end{code}

We define what it means for a property $P$ to hold on every member of an
ensemble $\alpha s$. We recurse through the ensemble, forking at unions. When
reaching a removal, the removed element is added to a list which accumulates
removed elements. For each element, we require either that $P$ holds for the
element, or else that it is in the list of removed elements.  Finally, $P$
holds on all of $\alpha s$ if it holds according to the above procedure, with
the removed element list starting empty.

\begin{code}

infixr 5 _all∪_
infixl 5 _all~_

data All_[_∖_] {A : Set} (P : Pred A) : Ensemble A → List A → Set₁ where
  all∅    : ∀{xs}    → All P [ ∅ ∖ xs ]
  all⟨_⟩  : ∀{xs α}  → P α         → All P [ ⟨ α ⟩ ∖ xs ]
  all-_   : ∀{xs α}  → α List.∈ xs → All P [ ⟨ α ⟩ ∖ xs ]
  _all~_  : ∀{αs xs} → ∀ x → All P [ αs ∖ x ∷ xs ] → All P [ αs - x ∖ xs ]
  _all∪_  : ∀{αs βs xs}
              → All P [ αs ∖ xs ] → All P [ βs ∖ xs ] → All P [ αs ∪ βs ∖ xs ]

All : {A : Set} → Pred A → Ensemble A → Set₁
All P αs = All P [ αs ∖ [] ]

\end{code}
