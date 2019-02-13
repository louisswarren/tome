open import Agda.Builtin.Equality

open import Decidable
open import List
  hiding (All ; all ; Any ; any)
  renaming (
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    decide∈    to decide[∈]    )

-- An ensemble is like a decidable finite set, but we do not define a
-- comprehension constructor.

infixr 5 _∷_ _∪_
infixl 5 _-_

data Ensemble {A : Set} (eq : Decidable≡ A) : Set where
  ∅   : Ensemble eq
  _∷_ : A           → Ensemble eq → Ensemble eq
  _-_ : Ensemble eq → A           → Ensemble eq
  _∪_ : Ensemble eq → Ensemble eq → Ensemble eq


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

private
  -- Some lemmae for All
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

-- All is decidable for decidable predicates
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


data Any_⟨_∖_⟩ {A : Set} {eq : Decidable≡ A} (P : Pred A) :
    Ensemble eq → List A → Set where
  [_,_] : ∀{αs xs α} → P α  → α [∉] xs              → Any P ⟨ α ∷ αs ∖ xs ⟩
  _∷_   : ∀{αs xs}   → ∀ α  → Any P ⟨ αs ∖ xs ⟩     → Any P ⟨ α ∷ αs ∖ xs ⟩
  _~_   : ∀{αs xs}   → ∀ x  → Any P ⟨ αs ∖ x ∷ xs ⟩ → Any P ⟨ αs - x ∖ xs ⟩
  _∣∪_  : ∀{βs xs}   → ∀ αs → Any P ⟨ βs ∖ xs ⟩     → Any P ⟨ αs ∪ βs ∖ xs ⟩
  _∪∣_  : ∀{αs xs}   → Any P ⟨ αs ∖ xs ⟩     → ∀ βs → Any P ⟨ αs ∪ βs ∖ xs ⟩

Any : {A : Set} {eq : Decidable≡ A} → (P : Pred A) → Ensemble eq → Set
Any P αs = Any P ⟨ αs ∖ [] ⟩

private
  -- Some lemmae for Any
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

-- Any is decidable for decidable predicates
any_⟨_∖_⟩ : {A : Set} {_≟_ : Decidable≡ A} {P : Pred A}
              → (p : Decidable P) → (αs : Ensemble _≟_) → (xs : List A)
              → Dec (Any P ⟨ αs ∖ xs ⟩)
any p ⟨ ∅ ∖ xs ⟩ = no λ ()
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


-- Any can be used to define membership
_∈_∖_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → List A → Set
α ∈ αs ∖ xs = Any (α ≡_) ⟨ αs ∖ xs ⟩

_∉_∖_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → List A → Set
α ∉ αs ∖ xs = ¬(α ∈ αs ∖ xs)

infix 4 _∈_ _∉_

_∈_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → Set
α ∈ αs = α ∈ αs ∖ []

_∉_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → Set
α ∉ αs = ¬(α ∈ αs)

-- Memberhsip is decidable since equality is decidable.
_∈?_ : {A : Set} {eq : Decidable≡ A}
       → (α : A) → (αs : Ensemble eq) → Dec (α ∈ αs)
_∈?_ {_} {eq} α αs = any (eq α) αs


-- Subsets follow from membership
_⊂_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Set
αs ⊂ βs = All (_∈ βs) αs

_⊂?_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Dec (αs ⊂ βs)
_⊂?_ {A} {_≟_} αs βs = all (λ x → any _≟_ x ⟨ βs ∖ [] ⟩) ⟨ αs ∖ [] ⟩
