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





lemma : ∀{α α′ β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β → β ≈ β′
        → β′ [ y / varterm x ]≡ α′ → α ≈ α′
lemma {α} y∉α (ident _ _) β≈β′ r rewrite subIdentFunc r = β≈β′
lemma {α} y∉α s β≈β′ (ident _ _) rewrite subIdentFunc s = β≈β′
lemma {α} y∉α (notfree x∉α) β≈β′ r with subNotFreeFunc r (≈notfree β≈β′ y∉α)
...                                | refl = β≈β′
lemma {α} y∉α s β≈β′ (notfree y∉β′) with subNotFreeFunc s (notfreeSub′ (≈notfree {!   !} y∉β′) s)
...                                 | refl = β≈β′
lemma {.(atom _ _)} y∉α (atom _ x) (atom _ ts) (atom _ x₁) = {!   !}
lemma {.(_ ⇒ _)} (y∉α ⇒ y∉α₁) (s ⇒ s₁) (β≈β′ ⇒ β≈β′₁) (r ⇒ r₁) = lemma y∉α s β≈β′ r ⇒ lemma y∉α₁ s₁ β≈β′₁ r₁
lemma {α} y∉α s (β≈β′ ∧ β≈β′₁) r = {!   !}
lemma {α} y∉α s (β≈β′ ∨ β≈β′₁) r = {!   !}
lemma {α} y∉α s (Λ x β≈β′) r = {!   !}
lemma {α} y∉α s (Λ/ x x₁ β≈β′) r = {!   !}
lemma {α} y∉α s (V x β≈β′) r = {!   !}
lemma {α} y∉α s (V/ x x₁ β≈β′) r = {!   !}


≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α
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

