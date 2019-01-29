\section{Ensemble.lagda}

Within a natural deduction proof, the context (collection of open assumptions)
must be manipulated. In particular, when an assumption is discharged it is
removed from the context. Some deductive rules require that a particular
variable not be free in any open assumption. At the end of a deduction, we
require that the remaining open assumptions are all contained within the
premise of the statement being derived. Both of these requirements involve
proving that a property holds on every remaining member of the context, but not
necessarily on assumptions that have been removed.  While removal of elements
from a list of formulae can be defined with a function, it is unweildy to give
proofs regarding the results of such computations, as they depend on
equality-checking of formulae, and so proofs must include both the case where
the equality is as expected, and the degenerate case. See \todo{appendix} for
details.

We define an extension of the list type, called ensemble. This has a
constructor for removal. While list concatenation does not have the same issues
as removal, concatenation of ensembles is nontrivial to compute due to this
constructor, and so a union constructor is also given. Ensembles are defined
only over types with decidable equality, so that it is always possible to
determine the elements of an ensemble. Note that this corresponds to finite
sets, as sets must be defined with an equality. However, no constructor is
given for comprehension.

\begin{code}

open import Agda.Builtin.Equality

open import Decidable
open import List
  hiding (All ; all ; Any ; any)
  renaming (
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    decide∈    to decide[∈]    )

infixr 5 _∷_
infixl 5 _∪_
infixl 5 _-_

data Ensemble {A : Set} (eq : Decidable≡ A) : Set where
  ∅   : Ensemble eq
  _∷_ : A           → Ensemble eq → Ensemble eq
  _-_ : Ensemble eq → A           → Ensemble eq
  _∪_ : Ensemble eq → Ensemble eq → Ensemble eq

\end{code}

We define what it means for a property $P$ to hold on every member of an
ensemble $\alpha s$. We recurse through the ensemble, forking at unions. When
reaching a removal constructor, the removed element is added to a list which
accumulates removed elements. For each element, we require either that $P$
holds for the element, or else that it is in the list of removed elements.
Finally, $P$ holds on all of $\alpha s$ if it holds according to the above
procedure, with the removed element list starting empty.

\begin{code}

infixr 5 _-∷_ _~_

data All_⟨_∖_⟩ {A : Set} {eq : Decidable≡ A} (P : Pred A) : Ensemble eq → List A → Set where
  ∅    : ∀{xs}       → All P ⟨ ∅ ∖ xs ⟩
  _∷_  : ∀{αs xs α}  → P α      → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _-∷_ : ∀{αs xs α}  → α [∈] xs → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _~_  : ∀{αs xs}    → ∀ x → All P ⟨ αs ∖ x ∷ xs ⟩ → All P ⟨ αs - x ∖ xs ⟩
  _∪_  : ∀{αs βs xs} → All P ⟨ αs ∖ xs ⟩ → All P ⟨ βs ∖ xs ⟩ → All P ⟨ αs ∪ βs ∖ xs ⟩

All : {A : Set} {_≟_ : Decidable≡ A} → (P : Pred A) → Ensemble _≟_ → Set
All P αs = All P ⟨ αs ∖ [] ⟩

\end{code}

If $P$ is decidable, then checking if $P$ holds in all of an ensemble is also
decidable. First, some lemmae for breaking down instances of the above
proposition:

\begin{code}

private
  headAll : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
            → All P ⟨ α ∷ αs ∖ xs ⟩ → α [∉] xs → P α
  headAll (Pα ∷ al)    α∉xs = Pα
  headAll (α∈xs -∷ al) α∉xs = ⊥-elim (α∉xs α∈xs)

  tailAll : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
            → All P ⟨ α ∷ αs ∖ xs ⟩ → All P ⟨ αs ∖ xs ⟩
  tailAll (_  ∷ ∀αs∖xsP) = ∀αs∖xsP
  tailAll (_ -∷ ∀αs∖xsP) = ∀αs∖xsP

  plusAll : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
            → All P ⟨ αs - α ∖ xs ⟩ → All P ⟨ αs ∖ α ∷ xs ⟩
  plusAll (_ ~ ∀αs∖α∷xs) = ∀αs∖α∷xs

  leftAll : ∀{A xs} {eq : Decidable≡ A} {αs βs : Ensemble eq} {P : Pred A}
            → All P ⟨ αs ∪ βs ∖ xs ⟩ → All P ⟨ αs ∖ xs ⟩
  leftAll (∀αs∖xsP ∪ _) = ∀αs∖xsP

  rightAll : ∀{A xs} {eq : Decidable≡ A} {αs βs : Ensemble eq} {P : Pred A}
            → All P ⟨ αs ∪ βs ∖ xs ⟩ → All P ⟨ βs ∖ xs ⟩
  rightAll (_ ∪ ∀βs∖xsP) = ∀βs∖xsP

\end{code}

Now we show decidability for all starting values for the accumulated list of
removed elements, and then in particular for starting with an empty list.

\begin{code}

all_⟨_∖_⟩ : {A : Set} {_≟_ : Decidable≡ A} {P : Pred A}
              → (P? : Decidable P) → (αs : Ensemble _≟_) → (xs : List A)
              → Dec (All P ⟨ αs ∖ xs ⟩)
all P? ⟨ ∅ ∖ xs ⟩ = yes ∅
all P? ⟨ α ∷ αs ∖ xs ⟩ with all P? ⟨ αs ∖ xs ⟩
...                                | no ¬all = no λ φ → ¬all (tailAll φ)
all_⟨_∖_⟩ {_} {_≟_} P? (α ∷ αs) xs | yes all with decide[∈] _≟_ α xs
...                                          | yes α∈xs = yes (α∈xs -∷ all)
...                                          | no  α∉xs with P? α
...                                                     | yes Pα = yes (Pα ∷ all)
...                                                     | no ¬Pα = no λ φ → ¬Pα (headAll φ α∉xs)
all P? ⟨ αs - α  ∖ xs ⟩ with all P? ⟨ αs ∖ α ∷ xs ⟩
...                     | yes all = yes (α ~ all)
...                     | no ¬all = no λ φ → ¬all (plusAll φ)
all P? ⟨ αs ∪ βs ∖ xs ⟩ with all P? ⟨ αs ∖ xs ⟩
...                     | no ¬allαs = no λ φ → ¬allαs (leftAll φ)
...                     | yes allαs with all P? ⟨ βs ∖ xs ⟩
...                                 | yes allβs = yes (allαs ∪ allβs)
...                                 | no ¬allβs = no λ φ → ¬allβs (rightAll φ)

all : {A : Set} {eq : Decidable≡ A} {P : Pred A}
      → (P? : Decidable P) → (αs : Ensemble eq) → Dec (All P αs)
all P? αs = all P? ⟨ αs ∖ [] ⟩

\end{code}

To define `Any' for ensembles, we also use an accumulating list for removed
elements, and require that the element satisfying $P$ not be in that list.

\begin{code}

data Any_⟨_∖_⟩ {A : Set} {eq : Decidable≡ A} (P : Pred A) : Ensemble eq → List A → Set where
  [_,_] : ∀{αs xs α} → P α  → α [∉] xs              → Any P ⟨ α ∷ αs ∖ xs ⟩
  _∷_   : ∀{αs xs}   → ∀ α  → Any P ⟨ αs ∖ xs ⟩     → Any P ⟨ α ∷ αs ∖ xs ⟩
  _~_   : ∀{αs xs}   → ∀ x  → Any P ⟨ αs ∖ x ∷ xs ⟩ → Any P ⟨ αs - x ∖ xs ⟩
  _∣∪_  : ∀{βs xs}   → ∀ αs → Any P ⟨ βs ∖ xs ⟩     → Any P ⟨ αs ∪ βs ∖ xs ⟩
  _∪∣_  : ∀{αs xs}   → Any P ⟨ αs ∖ xs ⟩     → ∀ βs → Any P ⟨ αs ∪ βs ∖ xs ⟩

Any : {A : Set} {eq : Decidable≡ A} → (P : Pred A) → Ensemble eq → Set
Any P αs = Any P ⟨ αs ∖ [] ⟩

\end{code}

Checking if a decidable property holds on any element of an ensemble is also
decidable.

\begin{code}

private
  hereAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
            → Any P ⟨ α ∷ αs ∖ xs ⟩ → ¬ Any P ⟨ αs ∖ xs ⟩ → P α
  hereAny [ Pα , _ ]    ¬∃αs∖xsP = Pα
  hereAny (_ ∷ ∃αs∖xsP) ¬∃αs∖xsP = ⊥-elim (¬∃αs∖xsP ∃αs∖xsP)

  laterAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
            → Any P ⟨ α ∷ αs ∖ xs ⟩ → ¬(P α) → Any P ⟨ αs ∖ xs ⟩
  laterAny [ Pα , _ ]    ¬Pα = ⊥-elim (¬Pα Pα)
  laterAny (_ ∷ ∃αs∖xsP) ¬Pα = ∃αs∖xsP

  thereAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
            → Any P ⟨ α ∷ αs ∖ xs ⟩ → α [∈] xs → Any P ⟨ αs ∖ xs ⟩
  thereAny [ _ , α[∉]xs ] α[∈]xs = ⊥-elim (α[∉]xs α[∈]xs)
  thereAny (_ ∷ ∃αs∖xs)   α[∈]xs = ∃αs∖xs

  plusAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
            → Any P ⟨ αs - α ∖ xs ⟩ → Any P ⟨ αs ∖ α ∷ xs ⟩
  plusAny (_ ~ ∃αs∖α∷xs) = ∃αs∖α∷xs

  leftAny : ∀{A xs} {eq : Decidable≡ A} {αs βs : Ensemble eq} {P : Pred A}
            → Any P ⟨ αs ∪ βs ∖ xs ⟩ → ¬ Any P ⟨ βs ∖ xs ⟩ → Any P ⟨ αs ∖ xs ⟩
  leftAny (αs      ∣∪  ∃βs∖xsP) ¬∃βs∖xsP = ⊥-elim (¬∃βs∖xsP ∃βs∖xsP)
  leftAny (∃αs∖xsP  ∪∣ βs)      ¬∃βs∖xsP = ∃αs∖xsP

  rightAny : ∀{A xs} {eq : Decidable≡ A} {αs βs : Ensemble eq} {P : Pred A}
            → Any P ⟨ αs ∪ βs ∖ xs ⟩ → ¬ Any P ⟨ αs ∖ xs ⟩ → Any P ⟨ βs ∖ xs ⟩
  rightAny (αs      ∣∪  ∃βs∖xsP) ¬∃αs∖xsP = ∃βs∖xsP
  rightAny (∃αs∖xsP  ∪∣ βs)      ¬∃αs∖xsP = ⊥-elim (¬∃αs∖xsP ∃αs∖xsP)


any_⟨_∖_⟩ : {A : Set} {_≟_ : Decidable≡ A} {P : Pred A}
              → (P? : Decidable P) → (αs : Ensemble _≟_) → (xs : List A)
              → Dec (Any P ⟨ αs ∖ xs ⟩)
any P? ⟨ ∅ ∖ xs ⟩ = no (λ ())
any P? ⟨ α ∷ αs  ∖ xs ⟩ with any P? ⟨ αs ∖ xs ⟩
...                                | yes any = yes (α ∷ any)
any_⟨_∖_⟩ {_} {_≟_} P? (α ∷ αs) xs | no ¬any with decide[∈] _≟_ α xs
...                                          | yes α∈xs = no λ φ → ¬any (thereAny φ α∈xs)
...                                          | no  α∉xs with P? α
...                                                     | yes Pα = yes [ Pα , α∉xs ]
...                                                     | no ¬Pα = no λ φ → ¬Pα (hereAny φ ¬any)
any P? ⟨ αs - α  ∖ xs ⟩ with any P? ⟨ αs ∖ α ∷ xs ⟩
...                     | yes any = yes (α ~ any)
...                     | no ¬any = no λ φ → ¬any (plusAny φ)
any P? ⟨ αs ∪ βs ∖ xs ⟩ with any P? ⟨ αs ∖ xs ⟩
...                     | yes anyαs = yes (anyαs ∪∣ βs)
...                     | no ¬anyαs with any P? ⟨ βs ∖ xs ⟩
...                                 | yes anyβs = yes (αs ∣∪ anyβs)
...                                 | no ¬anyβs = no λ φ → ¬anyβs (rightAny φ ¬anyαs)

any : {A : Set} {eq : Decidable≡ A} {P : Pred A}
      → (P? : Decidable P) → (αs : Ensemble eq) → Dec (Any P αs)
any P? αs = any P? ⟨ αs ∖ [] ⟩

\end{code}

As with lists, membership can be defined in terms of `All' and `Any'. Note that
membership is always decidable for ensembles.

\begin{code}

_∈_∖_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → List A → Set
α ∈ αs ∖ xs = Any (α ≡_) ⟨ αs ∖ xs ⟩

_∉_∖_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → List A → Set
α ∉ αs ∖ xs = ¬(α ∈ αs ∖ xs)


infix 4 _∈_ _∉_
_∈_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → Set
α ∈ αs = α ∈ αs ∖ []

_∉_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → Set
α ∉ αs = ¬(α ∈ αs)


_∈?_ : {A : Set} {eq : Decidable≡ A} → (α : A) → (αs : Ensemble eq) → Dec (α ∈ αs)
_∈?_ {_} {eq} α αs = any (eq α) αs

\end{code}

Subsets follow from membership.

\begin{code}

_⊂_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Set
αs ⊂ βs = All (_∈ βs) αs

_⊂?_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Dec (αs ⊂ βs)
_⊂?_ {A} {_≟_} αs βs = all (λ x → any _≟_ x ⟨ βs ∖ [] ⟩) ⟨ αs ∖ [] ⟩

\end{code}
