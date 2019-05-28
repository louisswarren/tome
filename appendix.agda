open import Agda.Builtin.Sigma

open import Decidable
open import Formula
open import Nat
open import Vec

-- Prove that ident is a derived rule. Note that this proof does not make use
-- of Formula.ident
derived-ident : ∀ α x → α [ x / varterm x ]≡ α
derived-ident (atom r ts) x = atom r (termsLemma ts)
  where
    termsLemma : ∀{n} → (ts : Vec Term n) → [ ts ][ x / varterm x ]≡ ts
    termsLemma [] = []
    termsLemma (varterm y     ∷ ts) with varEq x y
    ...                             | yes refl = varterm≡     ∷ termsLemma ts
    ...                             | no  x≢y  = varterm≢ x≢y ∷ termsLemma ts
    termsLemma (functerm f us ∷ ts) = functerm (termsLemma us) ∷ termsLemma ts
derived-ident (α ⇒ β) x = derived-ident α x ⇒ derived-ident β x
derived-ident (α ∧ β) x = derived-ident α x ∧ derived-ident β x
derived-ident (α ∨ β) x = derived-ident α x ∨ derived-ident β x
derived-ident (Λ y α) x with varEq x y
...             | yes refl = Λ∣ y α
...             | no  x≢y  = Λ x≢y (varterm y≢x) (derived-ident α x)
                             where
                               y≢x : y ≢ x
                               y≢x refl = x≢y refl
derived-ident (V y α) x with varEq x y
...             | yes refl = V∣ y α
...             | no  x≢y  = V x≢y (varterm y≢x) (derived-ident α x)
                             where
                               y≢x : y ≢ x
                               y≢x refl = x≢y refl


-- _FreeFor_In_ is decidable
_freeFor_In_ : ∀ t x α → Dec (t FreeFor x In α)
t freeFor x In α with x notFreeIn α
(t freeFor x In α) | yes xnfα = yes (notfree xnfα)
(t freeFor x In α) | no ¬xnfα = lemma α ¬xnfα
  where
    lemma : ∀ α → ¬(x NotFreeIn α)  → Dec (t FreeFor x In α)
    lemma (atom r ts) xf = yes (atom r ts)
    lemma (α ⇒ β)     xf with t freeFor x In α
    ...               | no ¬tffα = no ¬tffα⇒β
                                   where
                                     ¬tffα⇒β : _
                                     ¬tffα⇒β (notfree xnf) = xf xnf
                                     ¬tffα⇒β (tffα ⇒ _)     = ¬tffα tffα
    ...               | yes tffα with t freeFor x In β
    ...                          | no ¬tffβ = no ¬tffα⇒β
                                              where
                                                ¬tffα⇒β : _
                                                ¬tffα⇒β (notfree xnf) = xf xnf
                                                ¬tffα⇒β (_ ⇒ tffβ) = ¬tffβ tffβ
    ...                          | yes tffβ = yes (tffα ⇒ tffβ)
    lemma (α ∧ β)     xf with t freeFor x In α
    ...               | no ¬tffα = no ¬tffα∧β
                                   where
                                     ¬tffα∧β : _
                                     ¬tffα∧β (notfree xnf) = xf xnf
                                     ¬tffα∧β (tffα ∧ _)     = ¬tffα tffα
    ...               | yes tffα with t freeFor x In β
    ...                          | no ¬tffβ = no ¬tffα∧β
                                              where
                                                ¬tffα∧β : _
                                                ¬tffα∧β (notfree xnf) = xf xnf
                                                ¬tffα∧β (_ ∧ tffβ) = ¬tffβ tffβ
    ...                          | yes tffβ = yes (tffα ∧ tffβ)
    lemma (α ∨ β)     xf with t freeFor x In α
    ...               | no ¬tffα = no ¬tffα∨β
                                   where
                                     ¬tffα∨β : _
                                     ¬tffα∨β (notfree xnf) = xf xnf
                                     ¬tffα∨β (tffα ∨ _)     = ¬tffα tffα
    ...               | yes tffα with t freeFor x In β
    ...                          | no ¬tffβ = no ¬tffα∨β
                                              where
                                                ¬tffα∨β : _
                                                ¬tffα∨β (notfree xnf) = xf xnf
                                                ¬tffα∨β (_ ∨ tffβ) = ¬tffβ tffβ
    ...                          | yes tffβ = yes (tffα ∨ tffβ)
    lemma (Λ y α)     xf with varEq x y
    ...                  | yes refl = yes (Λ∣ α)
    ...                  | no  x≢y  with t freeFor x In α
    ...                             | no ¬tffα = no ¬tff
                                                 where
                                                   ¬tff : _
                                                   ¬tff (notfree xnf) = xf xnf
                                                   ¬tff (Λ∣ .α) = x≢y refl
                                                   ¬tff (Λ _ tffα) = ¬tffα tffα
    ...                             | yes tffα with y notInTerm t
    ...                                        | yes ynft = yes (Λ ynft tffα)
    ...                                        | no ¬ynft = no ¬tff
                                                            where
                                                              ¬tff : _
                                                              ¬tff (notfree xnf) = xf xnf
                                                              ¬tff (Λ∣ .α) = x≢y refl
                                                              ¬tff (Λ ynft _) = ¬ynft ynft
    lemma (V y α)     xf with varEq x y
    ...                  | yes refl = yes (V∣ α)
    ...                  | no  x≢y  with t freeFor x In α
    ...                             | no ¬tffα = no ¬tff
                                                 where
                                                   ¬tff : _
                                                   ¬tff (notfree xnf) = xf xnf
                                                   ¬tff (V∣ .α) = x≢y refl
                                                   ¬tff (V _ tffα) = ¬tffα tffα
    ...                             | yes tffα with y notInTerm t
    ...                                        | yes ynft = yes (V ynft tffα)
    ...                                        | no ¬ynft = no ¬tff
                                                            where
                                                              ¬tff : _
                                                              ¬tff (notfree xnf) = xf xnf
                                                              ¬tff (V∣ .α) = x≢y refl
                                                              ¬tff (V ynft _) = ¬ynft ynft


-- No guarantee that this notFree is tight - in fact for the V and Λ cases it is
-- not tight if the quantifier is the greatest variable (and does not have index
-- zero)
supFree : ∀ α → Σ ℕ λ ⌈α⌉ → ∀ n → ⌈α⌉ < n → var n NotFreeIn α
supFree (atom r ts) with supFreeTerms ts
supFree (atom r ts) | ⌈ts⌉ , tspf = ⌈ts⌉ , λ n ⌈ts⌉<n → atom (tspf n ⌈ts⌉<n)
supFree (α ⇒ β) with supFree α | supFree β
supFree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with ≤total ⌈α⌉ ⌈β⌉
supFree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → var n NotFreeIn (α ⇒ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ⇒ βpf n ⌈β⌉<n
supFree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → var n NotFreeIn (α ⇒ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ⇒ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supFree (α ∧ β) with supFree α | supFree β
supFree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with ≤total ⌈α⌉ ⌈β⌉
supFree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → var n NotFreeIn (α ∧ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∧ βpf n ⌈β⌉<n
supFree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → var n NotFreeIn (α ∧ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∧ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supFree (α ∨ β) with supFree α | supFree β
supFree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with ≤total ⌈α⌉ ⌈β⌉
supFree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → var n NotFreeIn (α ∨ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∨ βpf n ⌈β⌉<n
supFree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → var n NotFreeIn (α ∨ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∨ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supFree (Λ x α) with supFree α
supFree (Λ x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → Λ x (αpf n ⌈α⌉<n)
supFree (V x α) with supFree α
supFree (V x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → V x (αpf n ⌈α⌉<n)

unfree : ∀ α x → Σ Formula (λ β → Σ Variable λ y
         → Σ (x NotFreeIn β) λ _ → (β [ y / varterm x ]≡ α))
unfree α x with x notFreeIn α
...    | yes x∉α = α , x , x∉α , ident α x
...    | no ¬x∉α = β , y , subNotFree x∉y α[x/y]≡β , subInverse y∉α α[x/y]≡β
  where
    yfr : Σ Variable (_FreshIn α)
    yfr = fresh α
    y : Variable
    y = fst yfr
    y∉α : y NotFreeIn α
    y∉α = freshNotFree (snd yfr)
    x∉y : x NotInTerm (varterm y)
    x∉y = varterm λ { refl → ¬x∉α (freshNotFree (snd yfr)) }
    βsub : Σ Formula (α [ x / varterm y ]≡_)
    βsub = α [ x / freshFreeFor (snd yfr) x ]
    β : Formula
    β = fst βsub
    α[x/y]≡β : α [ x / varterm y ]≡ β
    α[x/y]≡β = snd βsub


-- todo: capitalisation
notfreeSub : ∀{α β x t z} → z NotFreeIn α → z NotInTerm t → α [ x / t ]≡ β → z NotFreeIn β
notfreeSub z∉α z∉t (ident α x) = z∉α
notfreeSub z∉α z∉t (notfree x∉α) = z∉α
notfreeSub (atom z∉us) z∉t (atom r sub) = atom (termsLemma z∉us z∉t sub)
  where
    termsLemma : ∀{n x t z} {us vs : Vec Term n} → z NotInTerms us
                 → z NotInTerm t → [ us ][ x / t ]≡ vs → z NotInTerms vs
    termsLemma z∉us z∉t [] = z∉us
    termsLemma (z∉u ∷ z∉us) z∉t (varterm≡ ∷ sub) = z∉t ∷ termsLemma z∉us z∉t sub
    termsLemma (z∉u ∷ z∉us) z∉t (varterm≢ x≢y ∷ sub) = z∉u ∷ termsLemma z∉us z∉t sub
    termsLemma (functerm z∉ts ∷ z∉us) z∉t (functerm subts ∷ sub) = functerm (termsLemma z∉ts z∉t subts) ∷ termsLemma z∉us z∉t sub
notfreeSub (z∉α ⇒ z∉β) z∉t (subα ⇒ subβ) = notfreeSub z∉α z∉t subα ⇒ notfreeSub z∉β z∉t subβ
notfreeSub (z∉α ∧ z∉β) z∉t (subα ∧ subβ) = notfreeSub z∉α z∉t subα ∧ notfreeSub z∉β z∉t subβ
notfreeSub (z∉α ∨ z∉β) z∉t (subα ∨ subβ) = notfreeSub z∉α z∉t subα ∨ notfreeSub z∉β z∉t subβ
notfreeSub z∉α z∉t (Λ∣ x α) = z∉α
notfreeSub z∉α z∉t (V∣ x α) = z∉α
notfreeSub (Λ∣ x α) z∉t (Λ x≢y y∉t sub) = Λ∣ x _
notfreeSub (V∣ x α) z∉t (V x≢y y∉t sub) = V∣ x _
notfreeSub (Λ y z∉α) z∉t (Λ x≢y y∉t sub) = Λ y (notfreeSub z∉α z∉t sub)
notfreeSub (V y z∉α) z∉t (V x≢y y∉t sub) = V y (notfreeSub z∉α z∉t sub)


notfreeSub′ : ∀{α β x y} → y NotFreeIn β → α [ x / varterm y ]≡ β → x NotFreeIn α
notfreeSub′ = ?

notfreeSub′′ : ∀{α β x t z} → z NotFreeIn β → z ≢ x → α [ x / t ]≡ β → z NotFreeIn α
notfreeSub′′ = ?

--todo: is it better to split this differently?
≈notfree : ∀{α α′ z} → α ≈ α′ → z NotFreeIn α → z NotFreeIn α′
≈notfree (atom r ts) (atom z∉ts) = atom z∉ts
≈notfree (α≈α′ ⇒ β≈β′) (z∉α ⇒ z∉β) = ≈notfree α≈α′ z∉α ⇒ ≈notfree β≈β′ z∉β
≈notfree (α≈α′ ∧ β≈β′) (z∉α ∧ z∉β) = ≈notfree α≈α′ z∉α ∧ ≈notfree β≈β′ z∉β
≈notfree (α≈α′ ∨ β≈β′) (z∉α ∨ z∉β) = ≈notfree α≈α′ z∉α ∨ ≈notfree β≈β′ z∉β
≈notfree (Λ x α≈α′) (Λ∣ .x α) = Λ∣ x _
≈notfree (V x α≈α′) (V∣ .x α) = V∣ x _
≈notfree {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′) (Λ∣ .x α) with varEq x y
...    | yes refl = Λ∣ x β′
...    | no  x≢y  = Λ y (≈notfree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β))
≈notfree {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′) (V∣ .x α) with varEq x y
...    | yes refl = V∣ x β′
...    | no  x≢y  = V y (≈notfree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β))
≈notfree (Λ y α≈α′) (Λ .y z∉α) = Λ y (≈notfree α≈α′ z∉α)
≈notfree (V y α≈α′) (V .y z∉α) = V y (≈notfree α≈α′ z∉α)
≈notfree {Λ x α} {Λ y β′} {z} (Λ/ y∉α α[x/y]≡β β≈β′) (Λ .x z∉α) with varEq z y
...    | yes refl = Λ∣ z β′
...    | no  z≢y  = Λ y (≈notfree β≈β′ (notfreeSub z∉α (varterm z≢y) α[x/y]≡β))
≈notfree {V x α} {V y β′} {z} (V/ y∉α α[x/y]≡β β≈β′) (V .x z∉α) with varEq z y
...    | yes refl = V∣ z β′
...    | no  z≢y  = V y (≈notfree β≈β′ (notfreeSub z∉α (varterm z≢y) α[x/y]≡β))


freeforSub : ∀{α β t x s y} → t FreeFor x In β → x ≢ y → α [ y / s ]≡ β → t FreeFor x In α
freeforSub (notfree x∉β) x≢y sub = notfree (notfreeSub′′ x∉β x≢y sub)
freeforSub ffβ x≢y (ident α x) = ffβ
freeforSub ffβ x≢y (notfree x∉α) = ffβ
freeforSub (atom r us) x≢y (atom .r x) = atom r _
freeforSub (ffβ ⇒ ffβ₁) x≢y (sub ⇒ sub₁) = freeforSub ffβ x≢y sub ⇒ freeforSub ffβ₁ x≢y sub₁
freeforSub (ffβ ∧ ffβ₁) x≢y (sub ∧ sub₁) = freeforSub ffβ x≢y sub ∧ freeforSub ffβ₁ x≢y sub₁
freeforSub (ffβ ∨ ffβ₁) x≢y (sub ∨ sub₁) = freeforSub ffβ x≢y sub ∨ freeforSub ffβ₁ x≢y sub₁
freeforSub (Λ∣ α) x≢y (Λ∣ x .α) = Λ∣ α
freeforSub (Λ∣ α) x≢y (Λ x x₁ sub) = Λ∣ _
freeforSub (V∣ α) x≢y (V∣ x .α) = V∣ α
freeforSub (V∣ α) x≢y (V x x₁ sub) = V∣ _
freeforSub (Λ x ffβ) x≢y (Λ∣ x₁ α) = Λ x ffβ
freeforSub (Λ x ffβ) x≢y (Λ x₁ x₂ sub) = Λ x (freeforSub ffβ x≢y sub)
freeforSub (V x ffβ) x≢y (V∣ x₁ α) = V x ffβ
freeforSub (V x ffβ) x≢y (V x₁ x₂ sub) = V x (freeforSub ffβ x≢y sub)

--subInverseWrap : ∀{ω α x v t β γ δ} → ω ≢ v → ω NotInTerm t → x ≢ v
--                 → α [ x / varterm ω ]≡ β → β [ v / t ]≡ γ
--                 → γ [ ω / varterm x ]≡ δ → α [ v / t ]≡ δ
--subInverseWrap = ?
--
--lemma : ∀{α α′ β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β → β ≈ β′
--        → β′ [ y / varterm x ]≡ α′ → α ≈ α′
--lemma {α} y∉α (ident _ _) β≈β′ r rewrite subIdentFunc r = β≈β′
--lemma {α} y∉α s β≈β′ (ident _ _) rewrite subIdentFunc s = β≈β′
--lemma {α} y∉α (notfree x∉α) β≈β′ r with subNotFreeFunc r (≈notfree β≈β′ y∉α)
--...                                | refl = β≈β′
--lemma {α} y∉α s β≈β′ (notfree y∉β′) with subNotFreeFunc s (notfreeSub′ (≈notfree {!   !} y∉β′) s)
--...                                 | refl = β≈β′
--lemma {.(atom _ _)} y∉α (atom _ x) (atom _ ts) (atom _ x₁) = {!   !}
--lemma {.(_ ⇒ _)} (y∉α ⇒ y∉α₁) (s ⇒ s₁) (β≈β′ ⇒ β≈β′₁) (r ⇒ r₁) = lemma y∉α s β≈β′ r ⇒ lemma y∉α₁ s₁ β≈β′₁ r₁
--lemma {.(_ ∧ _)} (y∉α ∧ y∉α₁) (s ∧ s₁) (β≈β′ ∧ β≈β′₁) (r ∧ r₁) = lemma y∉α s β≈β′ r ∧ lemma y∉α₁ s₁ β≈β′₁ r₁
--lemma {.(_ ∨ _)} (y∉α ∨ y∉α₁) (s ∨ s₁) (β≈β′ ∨ β≈β′₁) (r ∨ r₁) = lemma y∉α s β≈β′ r ∨ lemma y∉α₁ s₁ β≈β′₁ r₁
--lemma {.(Λ x α)} (Λ∣ .x .α) (Λ∣ .x α) (Λ x β≈β′) (Λ∣ .x α₁) = Λ x β≈β′
--lemma {.(Λ x α)} (Λ∣ .x .α) (Λ∣ .x α) (Λ x β≈β′) (Λ x₁ (varterm x₂) r) = ⊥-elim (x₂ refl)
--lemma {.(Λ _ α)} (Λ _ y∉α) (Λ∣ _ α) (Λ _ β≈β′) (Λ∣ _ α₁) = Λ _ β≈β′
--lemma {.(Λ _ α)} (Λ _ y∉α) (Λ∣ _ α) (Λ _ β≈β′) (Λ x (varterm x₁) r) = ⊥-elim (x₁ refl)
--lemma {.(Λ x _)} y∉α (Λ x₁ (varterm x₂) s) (Λ x β≈β′) (Λ∣ .x α) = ⊥-elim (x₂ refl)
--lemma {.(Λ x α)} (Λ∣ .x α) (Λ x₁ x₂ s) (Λ x β≈β′) (Λ x₃ x₄ r) = ⊥-elim (x₃ refl)
--lemma {.(Λ x _)} (Λ .x y∉α) (Λ x₁ x₂ s) (Λ x β≈β′) (Λ x₃ x₄ r) = Λ _ (lemma y∉α s β≈β′ r)
--lemma {.(Λ x₂ α)} y∉α (Λ∣ x₂ α) (Λ/ x x₁ β≈β′) (Λ∣ x₃ α₁) = Λ/ x x₁ β≈β′
--lemma {.(Λ x₂ α)} (Λ∣ .x₂ .α) (Λ∣ x₂ α) (Λ/ x x₁ β≈β′) (Λ x₃ x₄ r) rewrite subIdentFunc r = Λ/ x x₁ β≈β′
--lemma {.(Λ x₂ α)} (Λ .x₂ y∉α) (Λ∣ x₂ α) (Λ/ x x₁ β≈β′) (Λ x₃ x₄ r) with subNotFreeFunc r (≈notfree β≈β′ (notfreeSub y∉α (varterm x₃) x₁))
--lemma {.(Λ x₂ α)} (Λ .x₂ y∉α) (Λ∣ x₂ α) (Λ/ x x₁ β≈β′) (Λ x₃ x₄ r) | refl = Λ/ x x₁ β≈β′
--lemma {.(Λ x₄ α)} (Λ∣ x₄ α) (Λ x₂ (varterm x₃) s) (Λ/ x x₁ β≈β′) (Λ∣ .x₄ α₁) = ⊥-elim (x₃ refl)
--lemma {.(Λ x₄ α)} (Λ∣ x₄ α) (Λ x₂ (varterm x₃) s) (Λ/ x x₁ β≈β′) (Λ x₅ x₆ r) = ⊥-elim (x₃ refl)
--lemma {.(Λ y _)} (Λ y y∉α) (Λ x₂ x₃ s) (Λ/ x x₁ β≈β′) (Λ∣ x₄ α) with subNotFreeFunc s (notfreeSub′ x s)
--lemma {.(Λ y _)} (Λ y y∉α) (Λ x₂ x₃ s) (Λ/ x x₁ β≈β′) (Λ∣ x₄ α) | refl = Λ/ y∉α x₁ β≈β′
--lemma {Λ x α} {Λ .y α′} {Λ .x β} {Λ y γ′} {v} {w} (Λ .x w∉α) (Λ v≢x (varterm x≢w) s) (Λ/ {β = γ} y∉β β[x/y]≡γ γ≈γ′) (Λ w≢y (varterm y≢v) r) with subFunc ? ?
--... | refl = Λ/ (notfreeSub′′ y∉β y≢v s) (snd (α [ x / freeforSub (subFreeFor β[x/y]≡γ) (λ { refl → v≢x refl }) s ])) {! subUnique ? ?  !}
--lemma {α} y∉α s (V x β≈β′) r = {!   !}
--lemma {α} y∉α s (V/ x x₁ β≈β′) r = {!   !}

≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α

≈sub : ∀{α α′ β β′ x t} → α ≈ α′ → α [ x / t ]≡ β → α′ [ x / t ]≡ β′ → β ≈ β′
≈sub α≈α′ (ident α x) sub′ rewrite subIdentFunc sub′ = α≈α′
≈sub α≈α′ (notfree x) sub′ with subNotFreeFunc sub′ (≈notfree α≈α′ x)
... | refl = α≈α′
≈sub α≈α′ sub (ident α x) rewrite subIdentFunc sub = α≈α′
≈sub α≈α′ sub (notfree x) with subNotFreeFunc sub (≈notfree (≈sym α≈α′) x)
... | refl = α≈α′
≈sub (atom r ts) (atom .r x) (atom .r x₁) = {!   !}
≈sub (α≈α′ ⇒ α≈α′₁) (sub ⇒ sub₁) (sub′ ⇒ sub′₁) = ≈sub α≈α′ sub sub′ ⇒ ≈sub α≈α′₁ sub₁ sub′₁
≈sub (α≈α′ ∧ α≈α′₁) (sub ∧ sub₁) (sub′ ∧ sub′₁) = ≈sub α≈α′ sub sub′ ∧ ≈sub α≈α′₁ sub₁ sub′₁
≈sub (α≈α′ ∨ α≈α′₁) (sub ∨ sub₁) (sub′ ∨ sub′₁) = ≈sub α≈α′ sub sub′ ∨ ≈sub α≈α′₁ sub₁ sub′₁
≈sub (Λ x α≈α′) (Λ∣ .x α) (Λ∣ .x α₁) = Λ x α≈α′
≈sub (Λ x α≈α′) (Λ∣ .x α) (Λ x₁ x₂ sub′) = ⊥-elim (x₁ refl)
≈sub (Λ x α≈α′) (Λ x₁ x₂ sub) (Λ∣ .x α) = ⊥-elim (x₁ refl)
≈sub (Λ x α≈α′) (Λ x₁ x₂ sub) (Λ x₃ x₄ sub′) = Λ x (≈sub α≈α′ sub sub′)
≈sub (Λ/ x x₁ α≈α′) (Λ∣ x₂ α) (Λ∣ .x₂ α₁) = Λ/ x x₁ α≈α′
≈sub (Λ/ x x₁ α≈α′) (Λ∣ x₂ α) (Λ x₃ x₄ sub′) with subNotFreeFunc sub′ (≈notfree α≈α′ (subNotFree (varterm x₃) x₁))
≈sub (Λ/ x x₁ α≈α′) (Λ∣ x₂ α) (Λ x₃ x₄ sub′) | refl = Λ/ x x₁ α≈α′
≈sub (Λ/ x x₁ α≈α′) (Λ x₂ x₃ sub) (Λ∣ x₄ α) = Λ/ (subNotFree {!   !} sub) {!   !} {!   !}
≈sub (Λ/ x x₁ α≈α′) (Λ x₂ x₃ sub) (Λ x₄ x₅ sub′) = {!   !}
≈sub (V x α≈α′) sub sub′ = {! sub sub′  !}
≈sub (V/ x x₁ α≈α′) sub sub′ = {! sub sub′  !}


Λ/′ : ∀{α α′ β′ x y} → α ≈ α′ → y NotFreeIn α′ → α′ [ x / varterm y ]≡ β′ → Λ x α ≈ Λ y β′
Λ/′ α≈α′ y∉α′ sub = ?

≈sym (atom r ts) = atom r ts
≈sym (α≈α′ ⇒ β≈β′) = ≈sym α≈α′ ⇒ ≈sym β≈β′
≈sym (α≈α′ ∧ β≈β′) = ≈sym α≈α′ ∧ ≈sym β≈β′
≈sym (α≈α′ ∨ β≈β′) = ≈sym α≈α′ ∨ ≈sym β≈β′
≈sym (Λ x α≈α′) = Λ x (≈sym α≈α′)
≈sym {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = Λ x (≈sym β≈β′)
...    | no x≢y = ?
≈sym (V x α≈α′) = V x (≈sym α≈α′)
≈sym {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = V x (≈sym β≈β′)
...    | no x≢y = ?










--≈sub : ∀{α α′ β β′ x t} → α ≈ α′ → α [ x / t ]≡ β → α′ [ x / t ]≡ β′ → β ≈ β′

--≈trans : ∀{α α′ α′′} → α ≈ α′ → α′ ≈ α′′ → α ≈ α′′
--≈trans (atom r ts) (atom .r .ts) = atom r ts
--≈trans (α₁≈β₁ ⇒ α₂≈β₂) (β₁≈γ₁ ⇒ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ⇒ ≈trans α₂≈β₂ β₂≈γ₂
--≈trans (α₁≈β₁ ∧ α₂≈β₂) (β₁≈γ₁ ∧ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ∧ ≈trans α₂≈β₂ β₂≈γ₂
--≈trans (α₁≈β₁ ∨ α₂≈β₂) (β₁≈γ₁ ∨ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ∨ ≈trans α₂≈β₂ β₂≈γ₂
--≈trans (Λ x α≈α′) (Λ .x α′≈α′′) = Λ x (≈trans α≈α′ α′≈α′′)
--≈trans (Λ x α≈α′) (Λ/ y∉α′ α′[x/y]≡β β≈β′) = {!   !}
--≈trans (Λ x α≈α′) (Λ/′ ap2 x₁ x₂) = {!   !}
--≈trans (Λ/ x x₁ ap1) (Λ x₂ ap2) = {!   !}
--≈trans (Λ/ x x₁ ap1) (Λ/ x₂ x₃ ap2) = {!   !}
--≈trans (Λ/ x x₁ ap1) (Λ/′ ap2 x₂ x₃) = {!   !}
--≈trans (Λ/′ ap1 x x₁) (Λ x₂ ap2) = {!   !}
--≈trans (Λ/′ ap1 x x₁) (Λ/ x₂ x₃ ap2) = {!   !}
--≈trans (Λ/′ ap1 x x₁) (Λ/′ ap2 x₂ x₃) = {!   !}
--≈trans (V x ap1) (V .x ap2) = {!   !}
--≈trans (V x ap1) (V/ x₁ x₂ ap2) = {!   !}
--≈trans (V x ap1) (V/′ ap2 x₁ x₂) = {!   !}
--≈trans (V/ x x₁ ap1) (V x₂ ap2) = {!   !}
--≈trans (V/ x x₁ ap1) (V/ x₂ x₃ ap2) = {!   !}
--≈trans (V/ x x₁ ap1) (V/′ ap2 x₂ x₃) = {!   !}
--≈trans (V/′ ap1 x x₁) (V x₂ ap2) = {!   !}
--≈trans (V/′ ap1 x x₁) (V/ x₂ x₃ ap2) = {!   !}
--≈trans (V/′ ap1 x x₁) (V/′ ap2 x₂ x₃) = {!   !}

