-- These are proofs which aren't actually needed for doing natural deduction.

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma


open import Decidable
open import Formula
open import Deduction
open import Vec


-- The bulk of these proofs were generated with a mixture of Agda's auto and
-- vim macros. They are not very interesting, and all work by just breaking out
-- cases and examining them exhaustively.

-- Some formula propositions are decidable.

_doesNotOccurIn_ : (x : Variable) → (t : Term) → Dec (x DoesNotOccurIn t)
x doesNotOccurIn varterm x₁ with varEq x x₁
(x doesNotOccurIn varterm .x) | yes refl = no φ
  where φ : _
        φ (varterm x) = x refl
(x doesNotOccurIn varterm x₁) | no x₂ = yes (varterm x₂)
x doesNotOccurIn functerm (mkfunc idx .0) [] = yes (functerm [])
x doesNotOccurIn functerm (mkfunc idx (suc n)) (x₁ ∷ x₂) with (x doesNotOccurIn x₁) , (x doesNotOccurIn functerm (mkfunc idx n) x₂)
(x doesNotOccurIn functerm (mkfunc idx (suc _)) (x₁ ∷ x₂)) | yes x₃ , yes (functerm x₄) = yes (functerm (x₃ ∷ x₄))
(x doesNotOccurIn functerm (mkfunc idx (suc _)) (x₁ ∷ x₂)) | yes x₃ , no x₄ = no φ
  where φ : _
        φ (functerm (x₂ ∷ x₅)) = x₄ (functerm x₅)
(x doesNotOccurIn functerm (mkfunc idx (suc _)) (x₁ ∷ x₂)) | no x₃ , snd₁ = no φ
  where φ : _
        φ (functerm (x₄ ∷ x₅)) = x₃ x₄

_doesNotOccurInAny_ : ∀{n} → (x : Variable) → (ss : Vec Term n) → Dec (x DoesNotOccurInAny ss)
x doesNotOccurInAny ts = all (x doesNotOccurIn_) ts

_isBoundIn_ : (y : Variable) → (α : Formula) → Dec (y BoundIn α)
y isBoundIn atom r xs with y doesNotOccurInAny xs
(y isBoundIn atom r xs) | yes x = yes (atom x)
(y isBoundIn atom r xs) | no x = no φ
  where φ : _
        φ (atom x₁) = x x₁
y isBoundIn (α ⇒ β) with y isBoundIn α
(y isBoundIn (α ⇒ β)) | yes x with y isBoundIn β
(y isBoundIn (α ⇒ β)) | yes x | yes x₁ = yes (x ⇒ x₁)
(y isBoundIn (α ⇒ β)) | yes x | no x₁ = no φ
  where φ : _
        φ (pf ⇒ pf₁) = x₁ pf₁
(y isBoundIn (α ⇒ β)) | no x = no φ
  where φ : _
        φ (pf ⇒ pf₁) = x pf
y isBoundIn (α ∧ β) with y isBoundIn α
(y isBoundIn (α ∧ β)) | yes x with y isBoundIn β
(y isBoundIn (α ∧ β)) | yes x | yes x₁ = yes (x ∧ x₁)
(y isBoundIn (α ∧ β)) | yes x | no x₁ = no φ
  where φ : _
        φ (pf ∧ pf₁) = x₁ pf₁
(y isBoundIn (α ∧ β)) | no x = no φ
  where φ : _
        φ (pf ∧ pf₁) = x pf
y isBoundIn (α ∨ β) with y isBoundIn α
(y isBoundIn (α ∨ β)) | yes x with y isBoundIn β
(y isBoundIn (α ∨ β)) | yes x | yes x₁ = yes (x ∨ x₁)
(y isBoundIn (α ∨ β)) | yes x | no x₁ = no φ
  where φ : _
        φ (pf ∨ pf₁) = x₁ pf₁
(y isBoundIn (α ∨ β)) | no x = no φ
  where φ : _
        φ (pf ∨ pf₁) = x pf
y isBoundIn Λ x α with varEq y x
(.x isBoundIn Λ x α) | yes refl = yes (Λ∣ x α)
(y isBoundIn Λ x α) | no x₁ with y isBoundIn α
(y isBoundIn Λ x α) | no x₁ | yes x₂ = yes (Λ x x₂)
(y isBoundIn Λ x α) | no x₁ | no x₂ = no φ
  where φ : _
        φ (Λ∣ x α) = x₁ refl
        φ (Λ x pf) = x₂ pf
y isBoundIn V x α with varEq y x
(.x isBoundIn V x α) | yes refl = yes (V∣ x α)
(y isBoundIn V x α) | no x₁ with y isBoundIn α
(y isBoundIn V x α) | no x₁ | yes x₂ = yes (V x x₂)
(y isBoundIn V x α) | no x₁ | no x₂ = no φ
  where φ : _
        φ (V∣ x α) = x₁ refl
        φ (V x pf) = x₂ pf


-- Substitution of a term with itself does nothing.
-- While we prove this here, we give this as a constructor to aid automatic
-- proof search

identSub[] : ∀{n} → (x : Variable) → (xs : Vec Term n) → [ xs ][ x / varterm x ]≡ xs
identSub[] x [] = []
identSub[] x (varterm x₁ ∷ xs) with varEq x x₁
identSub[] x (varterm .x ∷ xs) | yes refl = var≡ x (identSub[] x xs)
identSub[] x (varterm x₁ ∷ xs) | no x₂ = var≢ x₁ x₂ (identSub[] x xs)
identSub[] x (functerm f x₁ ∷ xs) = func f (identSub[] x x₁) (identSub[] x xs)

coidentSub[] : ∀{n} → (x : Variable) → (xs ys : Vec Term n) → [ xs ][ x / varterm x ]≡ ys → xs ≡ ys
coidentSub[] x .[] .[] [] = refl
coidentSub[] x (varterm .x ∷ xs) (varterm .x ∷ ys) (var≡ .x r) with coidentSub[] x xs ys r
coidentSub[] x (varterm .x ∷ xs) (varterm .x ∷ .xs) (var≡ .x r) | refl = refl
coidentSub[] x (varterm .v ∷ xs) (varterm .v ∷ ys) (var≢ v x₁ r) with coidentSub[] x xs ys r
coidentSub[] x (varterm .v ∷ xs) (varterm .v ∷ .xs) (var≢ v x₁ r) | refl = refl
coidentSub[] x (functerm .f us ∷ xs) (functerm .f vs ∷ ys) (func f r r₁) with (coidentSub[] x xs ys r₁) , (coidentSub[] x us vs r)
coidentSub[] x (functerm .f us ∷ xs) (functerm .f .us ∷ .xs) (func f r r₁) | refl , refl = refl

-- Note that the constructor ident is not used here
identSub : (x : Variable) → (α : Formula) → α [ x / varterm x ]≡ α
identSub x (atom r x₁) = atom r (identSub[] x x₁)
identSub x (α ⇒ α₁) = identSub x α ⇒ identSub x α₁
identSub x (α ∧ α₁) = identSub x α ∧ identSub x α₁
identSub x (α ∨ α₁) = identSub x α ∨ identSub x α₁
identSub x (Λ x₁ α) with varEq x x₁
...                 | yes refl = Λ∣ x α
...                 | no x₂ = Λ x₂ (ident α x)
identSub x (V x₁ α) with varEq x x₁
...                 | yes refl = V∣ x α
...                 | no x₂ = V x₂ (ident α x)

coidentSub : (x : Variable) → (α β : Formula) → α [ x / varterm x ]≡ β → α ≡ β
coidentSub x α .α (ident .α .x) = refl
coidentSub x (atom .r us) (atom .r vs) (atom r x₁) with coidentSub[] x us vs x₁
coidentSub x (atom .r us) (atom .r .us) (atom r x₁) | refl = refl
coidentSub x (α ⇒ α₁) (β ⇒ β₁) (r ⇒ r₁) with (coidentSub x α β r) , (coidentSub x α₁ β₁ r₁)
coidentSub x (α ⇒ α₁) (.α ⇒ .α₁) (r ⇒ r₁) | refl , refl = refl
coidentSub x (α ∧ α₁) (β ∧ β₁) (r ∧ r₁) with (coidentSub x α β r) , (coidentSub x α₁ β₁ r₁)
coidentSub x (α ∧ α₁) (.α ∧ .α₁) (r ∧ r₁) | refl , refl = refl
coidentSub x (α ∨ α₁) (β ∨ β₁) (r ∨ r₁) with (coidentSub x α β r) , (coidentSub x α₁ β₁ r₁)
coidentSub x (α ∨ α₁) (.α ∨ .α₁) (r ∨ r₁) | refl , refl = refl
coidentSub x .(Λ x α) .(Λ x α) (Λ∣ .x α) = refl
coidentSub x .(V x α) .(V x α) (V∣ .x α) = refl
coidentSub x (Λ u α) (Λ .u β) (Λ x₂ r) with coidentSub x α β r
coidentSub x (Λ u α) (Λ .u .α) (Λ x₂ r) | refl = refl
coidentSub x (V u α) (V .u β) (V x₂ r) with coidentSub x α β r
coidentSub x (V u α) (V .u .α) (V x₂ r) | refl = refl


-- Every formula has a substitution

find[_][_/_] : ∀{n} → (xs : Vec Term n) → (x : Variable) → (t : Term) → Σ (Vec Term n) [ xs ][ x / t ]≡_
find[ [] ][ x / t ] = [] , []
find[ varterm x₁ ∷ xs ][ x / t ] with varEq x x₁
find[ varterm .x ∷ xs ][ x / t ] | yes refl with find[ xs ][ x / t ]
find[ varterm .x ∷ xs ][ x / t ] | yes refl | fst₁ , snd₁ = (t ∷ fst₁) , var≡ x snd₁
find[ varterm x₁ ∷ xs ][ x / t ] | no x₂ with find[ xs ][ x / t ]
find[ varterm x₁ ∷ xs ][ x / t ] | no x₂ | fst₁ , snd₁ = (varterm x₁ ∷ fst₁) , var≢ x₁ x₂ snd₁
find[ functerm f us ∷ xs ][ x / t ] with find[ us ][ x / t ] , find[ xs ][ x / t ]
find[ functerm f us ∷ xs ][ x / t ] | (fst₁ , snd₁) , fst₂ , snd₂ = (functerm f fst₁ ∷ fst₂) , func f snd₁ snd₂


find_[_/_] : (α : Formula) → (x : Variable) → (t : Term) → Σ Formula (α [ x / t ]≡_)
find atom r xs [ x / t ] with find[ xs ][ x / t ]
find atom r xs [ x / t ] | fst₁ , snd₁ = atom r fst₁ , atom r snd₁
find α ⇒ α₁ [ x / t ] with find α [ x / t ] , find α₁ [ x / t ]
find α ⇒ α₁ [ x / t ] | (fst₁ , snd₁) , fst₂ , snd₂ = fst₁ ⇒ fst₂ , snd₁ ⇒ snd₂
find α ∧ α₁ [ x / t ] with find α [ x / t ] , find α₁ [ x / t ]
find α ∧ α₁ [ x / t ] | (fst₁ , snd₁) , fst₂ , snd₂ = fst₁ ∧ fst₂ , snd₁ ∧ snd₂
find α ∨ α₁ [ x / t ] with find α [ x / t ] , find α₁ [ x / t ]
find α ∨ α₁ [ x / t ] | (fst₁ , snd₁) , fst₂ , snd₂ = fst₁ ∨ fst₂ , snd₁ ∨ snd₂
find Λ y α [ x / t ] with varEq x y
find Λ y α [ .y / t ] | yes refl = Λ y α , Λ∣ y α
find Λ y α [ x / t ] | no x₁ with find α [ x / t ]
find Λ y α [ x / t ] | no x₁ | fst₁ , snd₁ = Λ y fst₁ , Λ x₁ snd₁
find V y α [ x / t ] with varEq x y
find V y α [ .y / t ] | yes refl = V y α , V∣ y α
find V y α [ x / t ] | no x₁ with find α [ x / t ]
find V y α [ x / t ] | no x₁ | fst₁ , snd₁ = V y fst₁ , V x₁ snd₁

-- Substitution is unique

uniqueVSub : ∀{n} → (xs ys zs : Vec Term n) → ∀ x t → [ xs ][ x / t ]≡ ys → [ xs ][ x / t ]≡ zs → ys ≡ zs
uniqueVSub [] .[] .[] x t [] [] = refl
uniqueVSub (.(varterm x) ∷ xs) (.t ∷ ys) (.t ∷ zs) x t (var≡ .x ry) (var≡ .x rz) with uniqueVSub xs ys zs x t ry rz
uniqueVSub (.(varterm x) ∷ xs) (.t ∷ .zs) (.t ∷ zs) x t (var≡ .x ry) (var≡ .x rz) | refl = refl
uniqueVSub (.(varterm x) ∷ xs) (.t ∷ ys) (varterm .x ∷ zs) x t (var≡ .x ry) (var≢ .x x₁ rz) = ⊥-elim (x₁ refl)
uniqueVSub (.(varterm v) ∷ xs) (varterm .v ∷ ys) (.t ∷ zs) .v t (var≢ v x₁ ry) (var≡ .v rz) = ⊥-elim (x₁ refl)
uniqueVSub (.(varterm v) ∷ xs) (varterm .v ∷ ys) (varterm .v ∷ zs) x t (var≢ v x₁ ry) (var≢ .v x₂ rz) with uniqueVSub xs ys zs x t ry rz
uniqueVSub (.(varterm v) ∷ xs) (varterm .v ∷ .zs) (varterm .v ∷ zs) x t (var≢ v x₁ ry) (var≢ .v x₂ rz) | refl = refl
uniqueVSub ((functerm .f us) ∷ xs) (functerm .f vs ∷ ys) (functerm .f ws ∷ zs) x t (func f ry ry₁) (func .f rz rz₁)
    with (uniqueVSub us vs ws x t ry rz) , (uniqueVSub xs ys zs x t ry₁ rz₁)
uniqueVSub (functerm .f us ∷ xs) (functerm .f .ws ∷ .zs) (functerm .f ws ∷ zs) x t (func f ry ry₁) (func .f rz rz₁) | refl , refl = refl


uniqueSub : ∀ α β γ s t → α [ s / t ]≡ β → α [ s / t ]≡ γ → β ≡ γ
uniqueSub α .α γ s .(varterm s) (ident .α .s) rg = coidentSub s α γ rg
uniqueSub α β .α s .(varterm s) rb (ident .α .s) with coidentSub s α β rb
uniqueSub α .α .α s .(varterm s) rb (ident .α .s) | refl = refl
uniqueSub (atom r xs) (atom r ys) (atom r zs) s t (atom .r x) (atom .r x₁) with uniqueVSub xs ys zs s t x x₁
uniqueSub (atom r xs) (atom r .zs) (atom r zs) s t (atom .r x) (atom .r x₁) | refl = refl
uniqueSub (α ⇒ α₁) (β ⇒ β₁) (γ ⇒ γ₁) s t (rb ⇒ rb₁) (rg ⇒ rg₁)
    with (uniqueSub α β γ s t rb rg) , (uniqueSub α₁ β₁ γ₁ s t rb₁ rg₁)
... | refl , refl = refl
uniqueSub (α ∧ α₁) (β ∧ β₁) (γ ∧ γ₁) s t (rb ∧ rb₁) (rg ∧ rg₁)
    with (uniqueSub α β γ s t rb rg) , (uniqueSub α₁ β₁ γ₁ s t rb₁ rg₁)
... | refl , refl = refl
uniqueSub (α ∨ α₁) (β ∨ β₁) (γ ∨ γ₁) s t (rb ∨ rb₁) (rg ∨ rg₁)
    with (uniqueSub α β γ s t rb rg) , (uniqueSub α₁ β₁ γ₁ s t rb₁ rg₁)
... | refl , refl = refl
uniqueSub (Λ x α) (Λ x .α) (Λ x γ) .x t (Λ∣ _ _) (Λ∣ _ _) = refl
uniqueSub (Λ x α) (Λ x .α) (Λ x γ) .x t (Λ∣ _ _) (Λ x₁ rg) = ⊥-elim (x₁ refl)
uniqueSub (Λ x α) (Λ x β) (Λ x γ) .x t (Λ x₁ rb) (Λ∣ _ _) = ⊥-elim (x₁ refl)
uniqueSub (Λ x α) (Λ x β) (Λ x γ) s t (Λ x₁ rb) (Λ x₂ rg)
    with uniqueSub α β γ s t rb rg
... | refl = refl
uniqueSub (V x α) (V x .α) (V x γ) .x t (V∣ _ _) (V∣ _ _) = refl
uniqueSub (V x α) (V x .α) (V x γ) .x t (V∣ _ _) (V x₁ rg) = ⊥-elim (x₁ refl)
uniqueSub (V x α) (V x β) (V x γ)  .x t (V x₁ rb) (V∣ _ _) = ⊥-elim (x₁ refl)
uniqueSub (V x α) (V x β) (V x γ) s t (V x₁ rb) (V x₂ rg)
    with uniqueSub α β γ s t rb rg
... | refl = refl


-- Define a substitution operation, and check it

_[_/_] : Formula → Variable → Term → Formula
α [ x / t ] = fst find α [ x / t ]

subCorrect : ∀{α β s t} → α [ s / t ]≡ β → α [ s / t ] ≡ β
subCorrect {α} {β} {s} {t} rep with find α [ s / t ]
subCorrect {α} {β} {s} {t} rep | a′ , pf = uniqueSub α a′ β s t pf rep



-- An alternate (but harder to use) definition of existential introduction
existintropos : ∀{α Γ} → (r : Term) → (x : Variable)
               →                       Γ ⊢ α [ x / r ]
                                   ----------------------------- ∃⁺
               →                           Γ ⊢ V x α
existintropos {α} r x d with find α [ x / r ]
...                     | β , α[x/r]≡β = existintro r x α[x/r]≡β d
