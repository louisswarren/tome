-- These are proofs which aren't actually needed for doing natural deduction.

open import Agda.Builtin.Sigma


open import Decidable
open import Formula
open import Deduction
open import Vec


-- Some formula propositions are decidable

isTermNotIn : ∀{n} → (t : Term) → (ss : Vec Term n) → Dec (t TermNotIn ss)
isTermNotIn t [] = yes []
isTermNotIn t (s ∷ ss) with isTermNotIn t ss
isTermNotIn t (s ∷ ss) | yes rst with termEq t s
...                              | yes x = no φ
                                          where φ : _
                                                φ (var∉ _ neq _)    = neq x
                                                φ (func∉ _ _ neq _) = neq x

isTermNotIn t (varterm x₁ ∷ ss) | yes rst | no x = yes (var∉ x₁ x rst)
isTermNotIn t (functerm f x₁ ∷ ss) | yes rst | no x with isTermNotIn t x₁
isTermNotIn t (functerm f x₁ ∷ ss) | yes rst | no x | yes x₂ = yes (func∉ f x₂ x rst)
isTermNotIn t (functerm f x₁ ∷ ss) | yes rst | no x | no x₂ = no φ
                                                              where φ : _
                                                                    φ (func∉ f pf x₁ pf₁) = x₂ pf
isTermNotIn t (s ∷ ss) | no isin = no φ
                                  where φ : _
                                        φ (var∉ _ _ pf)    = isin pf
                                        φ (func∉ _ _ _ pf) = isin pf

-- Vim macros generated this
_isBoundIn_ : (t : Term) → (α : Formula) → Dec (t BoundIn α)
t isBoundIn atom r xs with isTermNotIn t xs
(t isBoundIn atom r xs) | yes x = yes (atom x)
(t isBoundIn atom r xs) | no x = no φ
  where φ : _
        φ (atom x₁) = x x₁
t isBoundIn (α ⇒ β) with t isBoundIn α
(t isBoundIn (α ⇒ β)) | yes x with t isBoundIn β
(t isBoundIn (α ⇒ β)) | yes x | yes x₁ = yes (x ⇒ x₁)
(t isBoundIn (α ⇒ β)) | yes x | no x₁ = no φ
  where φ : _
        φ (pf ⇒ pf₁) = x₁ pf₁
(t isBoundIn (α ⇒ β)) | no x = no φ
  where φ : _
        φ (pf ⇒ pf₁) = x pf
t isBoundIn (α ∧ β) with t isBoundIn α
(t isBoundIn (α ∧ β)) | yes x with t isBoundIn β
(t isBoundIn (α ∧ β)) | yes x | yes x₁ = yes (x ∧ x₁)
(t isBoundIn (α ∧ β)) | yes x | no x₁ = no φ
  where φ : _
        φ (pf ∧ pf₁) = x₁ pf₁
(t isBoundIn (α ∧ β)) | no x = no φ
  where φ : _
        φ (pf ∧ pf₁) = x pf
t isBoundIn (α ∨ β) with t isBoundIn α
(t isBoundIn (α ∨ β)) | yes x with t isBoundIn β
(t isBoundIn (α ∨ β)) | yes x | yes x₁ = yes (x ∨ x₁)
(t isBoundIn (α ∨ β)) | yes x | no x₁ = no φ
  where φ : _
        φ (pf ∨ pf₁) = x₁ pf₁
(t isBoundIn (α ∨ β)) | no x = no φ
  where φ : _
        φ (pf ∨ pf₁) = x pf
t isBoundIn Λ x α with termEq t (varterm x)
(.(varterm x) isBoundIn Λ x α) | yes refl = yes (Λ∣ x α)
(t isBoundIn Λ x α) | no x₁ with t isBoundIn α
(t isBoundIn Λ x α) | no x₁ | yes x₂ = yes (Λ x x₂)
(t isBoundIn Λ x α) | no x₁ | no x₂ = no φ
  where φ : _
        φ (Λ∣ x α) = x₁ refl
        φ (Λ x pf) = x₂ pf
t isBoundIn V x α with termEq t (varterm x)
(.(varterm x) isBoundIn V x α) | yes refl = yes (V∣ x α)
(t isBoundIn V x α) | no x₁ with t isBoundIn α
(t isBoundIn V x α) | no x₁ | yes x₂ = yes (V x x₂)
(t isBoundIn V x α) | no x₁ | no x₂ = no φ
  where φ : _
        φ (V∣ x α) = x₁ refl
        φ (V x pf) = x₂ pf


-- Substitution of a term with itself does nothing.
-- While we prove this here, we give this as a constructor to aid automatic
-- proof search

identSub[] : ∀{n} → (t : Term) → (xs : Vec Term n) → [ xs ][ t / t ]≡ xs
identSub[] t [] = []
identSub[] t (varterm x ∷ xs) with termEq t (varterm x)
identSub[] .(varterm x) (varterm x ∷ xs) | yes refl = var≡ x (identSub[] (varterm x) xs)
identSub[] t (varterm x ∷ xs) | no x₁ = var≢ x x₁ (identSub[] t xs)
identSub[] t (functerm f x ∷ xs) with termEq t (functerm f x)
identSub[] .(functerm f x) (functerm f x ∷ xs) | yes refl = func≡ f (identSub[] (functerm f x) xs)
identSub[] t (functerm f x ∷ xs) | no x₁ = func≢ f x₁ (identSub[] t x) (identSub[] t xs)

coidentSub[] : ∀{n} → (t : Term) → (xs ys : Vec Term n) → [ xs ][ t / t ]≡ ys → xs ≡ ys
coidentSub[] t [] .[] [] = refl
coidentSub[] .(varterm x₁) (.(varterm x₁) ∷ xs) (varterm .x₁ ∷ ys) (var≡ x₁ x₂) with coidentSub[] (varterm x₁) xs ys x₂
coidentSub[] .(varterm x₁) (.(varterm x₁) ∷ xs) (varterm .x₁ ∷ .xs) (var≡ x₁ x₂) | refl = refl
coidentSub[] t (.(varterm x₁) ∷ xs) (varterm .x₁ ∷ ys) (var≢ x₁ x₂ x₃) with coidentSub[] t xs ys x₃
coidentSub[] t (.(varterm x₁) ∷ xs) (varterm .x₁ ∷ .xs) (var≢ x₁ x₂ x₃) | refl = refl
coidentSub[] t (.(functerm f _) ∷ xs) (functerm .f _ ∷ ys) (func≡ f x₁) with coidentSub[] t xs ys x₁
coidentSub[] .(functerm f _) (.(functerm f _) ∷ xs) (functerm .f _ ∷ .xs) (func≡ f x₁) | refl = refl
coidentSub[] t ((functerm .f us) ∷ xs) (functerm .f vs ∷ ys) (func≢ f x₁ x₂ x₃) with (coidentSub[] t xs ys x₃) , (coidentSub[] t us vs x₂)
coidentSub[] t ((functerm .f us) ∷ xs) (functerm .f vs ∷ .xs) (func≢ f x₁ x₂ x₃) | refl , refl = refl

identSub : (t : Term) → (α : Formula) → α [ t / t ]≡ α
identSub t (atom r x) = atom r (identSub[] t x)
identSub t (α ⇒ α₁) = identSub t α ⇒ identSub t α₁
identSub t (α ∧ α₁) = identSub t α ∧ identSub t α₁
identSub t (α ∨ α₁) = identSub t α ∨ identSub t α₁
identSub t (Λ x α) with termEq t (varterm x)
...               | yes refl = Λ∣
...               | no x₁ = Λ x₁ (identSub t α)
identSub t (V x α) with termEq t (varterm x)
...               | yes refl = V∣
...               | no x₁ = V x₁ (identSub t α)

coidentSub : (t : Term) → (α β : Formula) → α [ t / t ]≡ β → α ≡ β
coidentSub t (atom r₁ x₁) .(atom r₁ x₁) (ident .(atom r₁ x₁) .t) = refl
coidentSub t (atom r₁ x₁) (atom .r₁ x₂) (atom .r₁ x₃) with coidentSub[] t x₁ x₂ x₃
coidentSub t (atom r₁ x₁) (atom .r₁ .x₁) (atom .r₁ x₃) | refl = refl
coidentSub t (α ⇒ α₁) .(α ⇒ α₁) (ident .(α ⇒ α₁) .t) = refl
coidentSub t (α ⇒ α₁) (β ⇒ β₁) (r ⇒ r₁) with (coidentSub t α β r) , (coidentSub t α₁ β₁ r₁)
coidentSub t (α ⇒ α₁) (.α ⇒ .α₁) (r ⇒ r₁) | refl , refl = refl
coidentSub t (α ∧ α₁) .(α ∧ α₁) (ident .(α ∧ α₁) .t) = refl
coidentSub t (α ∧ α₁) (β ∧ β₁) (r ∧ r₁) with (coidentSub t α β r) , (coidentSub t α₁ β₁ r₁)
coidentSub t (α ∧ α₁) (.α ∧ .α₁) (r ∧ r₁) | refl , refl = refl
coidentSub t (α ∨ α₁) .(α ∨ α₁) (ident .(α ∨ α₁) .t) = refl
coidentSub t (α ∨ α₁) (β ∨ β₁) (r ∨ r₁) with (coidentSub t α β r) , (coidentSub t α₁ β₁ r₁)
coidentSub t (α ∨ α₁) (.α ∨ .α₁) (r ∨ r₁) | refl , refl = refl
coidentSub t (Λ x₁ α) .(Λ x₁ α) (ident .(Λ x₁ α) .t) = refl
coidentSub .(varterm x₁) (Λ x₁ α) .(Λ x₁ α) Λ∣ = refl
coidentSub t (Λ x₁ α) (Λ .x₁ β) (Λ x₂ r) with coidentSub t α β r
coidentSub t (Λ x₁ α) (Λ .x₁ .α) (Λ x₂ r) | refl = refl
coidentSub t (V x₁ α) .(V x₁ α) (ident .(V x₁ α) .t) = refl
coidentSub .(varterm x₁) (V x₁ α) .(V x₁ α) V∣ = refl
coidentSub t (V x₁ α) (V .x₁ β) (V x₂ r) with coidentSub t α β r
coidentSub t (V x₁ α) (V .x₁ .α) (V x₂ r) | refl = refl


-- Substitution is unique

uniqueVSub : ∀{n} → (xs ys zs : Vec Term n) → ∀ s t → [ xs ][ s / t ]≡ ys → [ xs ][ s / t ]≡ zs → ys ≡ zs
uniqueVSub [] .[] .[] s t [] [] = refl
uniqueVSub (.(varterm x) ∷ xs) (.t ∷ ys) (.t ∷ zs) .(varterm x) t (var≡ x ry) (var≡ .x rz) with uniqueVSub xs ys zs (varterm x) t ry rz
uniqueVSub (.(varterm x) ∷ xs) (.t ∷ .zs) (.t ∷ zs) .(varterm x) t (var≡ x ry) (var≡ .x rz) | refl = refl
uniqueVSub (.(varterm x) ∷ xs) (.t ∷ ys) (.(varterm x) ∷ zs) .(varterm x) t (var≡ x ry) (var≢ .x x₂ rz) = ⊥-elim (x₂ refl)
uniqueVSub (.(varterm x) ∷ xs) .(varterm x ∷ _) .(t ∷ _) .(varterm x) t (var≢ x x₁ ry) (var≡ .x rz) = ⊥-elim (x₁ refl)
uniqueVSub (.(varterm x) ∷ xs) (.(varterm x) ∷ ys) (.(varterm x) ∷ zs) s t (var≢ x x₁ ry) (var≢ .x x₂ rz) with uniqueVSub xs ys zs s t ry rz
uniqueVSub (.(varterm x) ∷ xs) (.(varterm x) ∷ .zs) (.(varterm x) ∷ zs) s t (var≢ x x₁ ry) (var≢ .x x₂ rz) | refl = refl
uniqueVSub ((functerm .f us) ∷ xs) (.t ∷ ys) (.t ∷ zs) .(functerm f us) t (func≡ f ry) (func≡ .f rz) with uniqueVSub xs ys zs (functerm f us) t ry rz
uniqueVSub (functerm .f us ∷ xs) (.t ∷ .zs) (.t ∷ zs) .(functerm f us) t (func≡ f ry) (func≡ .f rz) | refl = refl
uniqueVSub (.(functerm f _) ∷ xs) (_ ∷ ys) .(functerm f _ ∷ _) .(functerm f _) _ (func≡ f ry) (func≢ .f x₁ rz rz₁) = ⊥-elim (x₁ refl)
uniqueVSub (.(functerm f _) ∷ xs) .(functerm f _ ∷ _) .(t ∷ _) .(functerm f _) t (func≢ f x ry ry₁) (func≡ .f rz) = ⊥-elim (x refl)
uniqueVSub ((functerm .f us) ∷ xs) ((functerm .f vs) ∷ ys) ((functerm .f ws) ∷ zs) s t (func≢ f x ry ry₁) (func≢ .f x₁ rz rz₁)
    with (uniqueVSub us vs ws s t ry rz) , (uniqueVSub xs ys zs s t ry₁ rz₁)
... | refl , refl = refl

uniqueSub : ∀ α β γ s t → α [ s / t ]≡ β → α [ s / t ]≡ γ → β ≡ γ
uniqueSub α .α γ s .s (ident .α .s) rg = coidentSub s α γ rg
uniqueSub α β .α s .s rb (ident .α .s) with coidentSub s α β rb
uniqueSub α .α .α s .s rb (ident .α .s) | refl = refl
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
uniqueSub (Λ x α) (Λ x .α) (Λ x γ) .(varterm x) t Λ∣ Λ∣ = refl
uniqueSub (Λ x α) (Λ x .α) (Λ x γ) .(varterm x) t Λ∣ (Λ x₁ rg) = ⊥-elim (x₁ refl)
uniqueSub (Λ x α) (Λ x β) (Λ x γ) .(varterm x) t (Λ x₁ rb) Λ∣ = ⊥-elim (x₁ refl)
uniqueSub (Λ x α) (Λ x β) (Λ x γ) s t (Λ x₁ rb) (Λ x₂ rg)
    with uniqueSub α β γ s t rb rg
... | refl = refl
uniqueSub (V x α) (V x .α) (V x γ) .(varterm x) t V∣ V∣ = refl
uniqueSub (V x α) (V x .α) (V x γ) .(varterm x) t V∣ (V x₁ rg) = ⊥-elim (x₁ refl)
uniqueSub (V x α) (V x β) (V x γ) .(varterm x) t (V x₁ rb) V∣ = ⊥-elim (x₁ refl)
uniqueSub (V x α) (V x β) (V x γ) s t (V x₁ rb) (V x₂ rg)
    with uniqueSub α β γ s t rb rg
... | refl = refl

repWitness : ∀{α β s t} → α [ s / t ]≡ β → α [ s / t ] ≡ β
repWitness {α} {β} {s} {t} rep with find α [ s / t ]
repWitness {α} {β} {s} {t} rep | a′ , pf = uniqueSub α a′ β s t pf rep


-- An alternate (but harder to use) definition of existential introduction
existintropos : ∀{α Γ} → (r : Term) → (x : Variable)
               →                       Γ ⊢ α [ varterm x / r ]
                                   ----------------------------- ∃⁺
               →                           Γ ⊢ V x α
existintropos {α} r x d with find α [ varterm x / r ]
...                     | β , α[x/r]≡β = existintro r x α[x/r]≡β d