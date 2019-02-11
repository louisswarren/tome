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

infixr 5 _∷_ _∪_
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

data All_⟨_∖_⟩ {A : Set} {eq : Decidable≡ A} (P : Pred A) :
    Ensemble eq → List A → Set where
  ∅    : ∀{xs}       → All P ⟨ ∅ ∖ xs ⟩
  _∷_  : ∀{αs xs α}  → P α      → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _-∷_ : ∀{αs xs α}  → α [∈] xs → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _~_  : ∀{αs xs}    → ∀ x → All P ⟨ αs ∖ x ∷ xs ⟩ → All P ⟨ αs - x ∖ xs ⟩
  _∪_  : ∀{αs βs xs} → All P ⟨ αs ∖ xs ⟩ → All P ⟨ βs ∖ xs ⟩
                     → All P ⟨ αs ∪ βs ∖ xs ⟩

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
              → (p : Decidable P) → (αs : Ensemble _≟_) → (xs : List A)
              → Dec (All P ⟨ αs ∖ xs ⟩)
all p ⟨ ∅ ∖ xs ⟩ = yes ∅
all_⟨_∖_⟩ {_} {eq} p (α ∷ αs) xs with decide[∈] eq α xs
all_⟨_∖_⟩ {_} {eq} p (α ∷ αs) xs | no α∉xs with p α
... | no ¬Pα = no λ f → ¬Pα (headAll f α∉xs)
... | yes Pα with all p ⟨ αs ∖ xs ⟩
...          | yes Pαs = yes (Pα ∷ Pαs)
...          | no ¬Pαs = no λ φ → ¬Pαs (tailAll φ)
all_⟨_∖_⟩ {_} {eq} p (α ∷ αs) xs | yes α∈xs with all p ⟨ αs ∖ xs ⟩
... | yes Pαs = yes (α∈xs -∷ Pαs)
... | no ¬Pαs = no λ φ → ¬Pαs (tailAll φ)
all p ⟨ αs - α ∖ xs ⟩  with all p ⟨ αs ∖ α ∷ xs ⟩
...                    | yes Pαs = yes (α ~ Pαs)
...                    | no ¬Pαs = no λ φ → ¬Pαs (plusAll φ)
all p ⟨ αs ∪ βs ∖ xs ⟩ with all p ⟨ αs ∖ xs ⟩ | all p ⟨ βs ∖ xs ⟩
...                    | yes Pαs | yes Pβs = yes (Pαs ∪ Pβs)
...                    | no ¬Pαs | _       = no λ φ → ¬Pαs (leftAll φ)
...                    | _       | no ¬Pβs = no λ φ → ¬Pβs (rightAll φ)

all : {A : Set} {eq : Decidable≡ A} {P : Pred A}
      → (p : Decidable P) → (αs : Ensemble eq) → Dec (All P αs)
all p αs = all p ⟨ αs ∖ [] ⟩

\end{code}

To define `Any' for ensembles, we also use an accumulating list for removed
elements, and require that the element satisfying $P$ not be in that list.

\begin{code}

data Any_⟨_∖_⟩ {A : Set} {eq : Decidable≡ A} (P : Pred A) :
    Ensemble eq → List A → Set where
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

  thereAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
            → Any P ⟨ α ∷ αs ∖ xs ⟩ → α [∈] xs → Any P ⟨ αs ∖ xs ⟩
  thereAny [ _ , α[∉]xs ] α[∈]xs = ⊥-elim (α[∉]xs α[∈]xs)
  thereAny (_ ∷ ∃αs∖xs)   α[∈]xs = ∃αs∖xs

  plusAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
            → Any P ⟨ αs - α ∖ xs ⟩ → Any P ⟨ αs ∖ α ∷ xs ⟩
  plusAny (_ ~ ∃αs∖α∷xs) = ∃αs∖α∷xs

  unionAny : ∀{A xs} {eq : Decidable≡ A} {αs βs : Ensemble eq} {P : Pred A}
            → {Φ : Set}
            → Any P ⟨ αs ∪ βs ∖ xs ⟩
            → (Any P ⟨ αs ∖ xs ⟩ → Φ) → (Any P ⟨ βs ∖ xs ⟩ → Φ) → Φ
  unionAny (αs ∣∪ ∃βsP) ∃αsP→Φ ∃βsP→Φ = ∃βsP→Φ ∃βsP
  unionAny (∃αsP ∪∣ βs) ∃αsP→Φ ∃βsP→Φ = ∃αsP→Φ ∃αsP


any_⟨_∖_⟩ : {A : Set} {_≟_ : Decidable≡ A} {P : Pred A}
              → (p : Decidable P) → (αs : Ensemble _≟_) → (xs : List A)
              → Dec (Any P ⟨ αs ∖ xs ⟩)
any p ⟨ ∅ ∖ xs ⟩ = no (λ ())
any_⟨_∖_⟩ {_} {eq} p (α ∷ αs) xs with decide[∈] eq α xs
any_⟨_∖_⟩ {_} {eq} p (α ∷ αs) xs | no α∉xs with p α
... | yes Pα = yes [ Pα , α∉xs ]
... | no ¬Pα with any p ⟨ αs ∖ xs ⟩
...          | yes ∃αsP = yes (α ∷ ∃αsP)
...          | no ¬∃αsP = no λ φ → ¬Pα (hereAny φ ¬∃αsP)
any_⟨_∖_⟩ {_} {eq} p (α ∷ αs) xs | yes α∈xs with any p ⟨ αs ∖ xs ⟩
... | yes ∃αsP = yes (α ∷ ∃αsP)
... | no ¬∃αsP = no λ φ → ¬∃αsP (thereAny φ α∈xs)
any p ⟨ αs - α ∖ xs ⟩  with any p ⟨ αs ∖ α ∷ xs ⟩
...                    | yes ∃αsP = yes (α ~ ∃αsP)
...                    | no ¬∃αsP = no λ φ → ¬∃αsP (plusAny φ)
any p ⟨ αs ∪ βs ∖ xs ⟩ with any p ⟨ αs ∖ xs ⟩ | any p ⟨ βs ∖ xs ⟩
...                    | yes ∃αsP | _        = yes (∃αsP ∪∣ βs)
...                    | _        | yes ∃βsP = yes (αs ∣∪ ∃βsP)
any p ⟨ αs ∪ βs ∖ xs ⟩ | no ¬∃αsP | no ¬∃βsP = no λ φ → unionAny φ ¬∃αsP ¬∃βsP

any : {A : Set} {eq : Decidable≡ A} {P : Pred A}
      → (p : Decidable P) → (αs : Ensemble eq) → Dec (Any P αs)
any p αs = any p ⟨ αs ∖ [] ⟩

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


_∈?_ : {A : Set} {eq : Decidable≡ A}
       → (α : A) → (αs : Ensemble eq) → Dec (α ∈ αs)
_∈?_ {_} {eq} α αs = any (eq α) αs

\end{code}

Subsets follow from membership.

\begin{code}

_⊂_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Set
αs ⊂ βs = All (_∈ βs) αs

_⊂?_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Dec (αs ⊂ βs)
_⊂?_ {A} {_≟_} αs βs = all (λ x → any _≟_ x ⟨ βs ∖ [] ⟩) ⟨ αs ∖ [] ⟩

\end{code}
