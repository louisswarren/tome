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
    ...                             | yes tffα with y notFreeInTerm t
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
    ...                             | yes tffα with y notFreeInTerm t
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


≈refl : ∀{α} → α ≈ α
≈refl {atom r ts} = atom r ts
≈refl {α ⇒ β} = ≈refl ⇒ ≈refl
≈refl {α ∧ β} = ≈refl ∧ ≈refl
≈refl {α ∨ β} = ≈refl ∨ ≈refl
≈refl {Λ x α} = Λ x ≈refl
≈refl {V x α} = V x ≈refl

≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α
≈notfree : ∀{x α α′} → α ≈ α′ → x NotFreeIn α → x NotFreeIn α′

≈sub : ∀{α α′ β β′ x t} → α ≈ α′ → α [ x / t ]≡ β → α′ [ x / t ]≡ β′ → β ≈ β′
≈sub = ?


≈notfree = ?

≈trans : ∀{α β γ} → α ≈ β → β ≈ γ → α ≈ γ
≈trans (atom r ts) (atom .r .ts) = atom r ts
≈trans (α≈β ⇒ α≈β₁) (β≈γ ⇒ β≈γ₁) = ≈trans α≈β β≈γ ⇒ ≈trans α≈β₁ β≈γ₁
≈trans (α≈β ∧ α≈β₁) (β≈γ ∧ β≈γ₁) = ≈trans α≈β β≈γ ∧ ≈trans α≈β₁ β≈γ₁
≈trans (α≈β ∨ α≈β₁) (β≈γ ∨ β≈γ₁) = ≈trans α≈β β≈γ ∨ ≈trans α≈β₁ β≈γ₁
≈trans (Λ x α≈β) (Λ .x β≈γ) = Λ x (≈trans α≈β β≈γ)
≈trans (Λ x α≈α′) (Λ/ y∉α′ α′[x/y]≡β β≈β′) = Λ/ (≈notfree (≈sym α≈α′) y∉α′) {!   !} {!   !}
  where
    γ : Formula
    γ : fst (α 
≈trans (Λ/ x x₁ α≈β) (Λ x₂ β≈γ) = Λ/ x x₁ (≈trans α≈β β≈γ)
≈trans (Λ/ x x₁ α≈β) (Λ/ x₂ x₃ β≈γ) = {!   !}
≈trans (V x α≈β) (V .x β≈γ) = V x (≈trans α≈β β≈γ)
≈trans (V x α≈β) (V/ x₁ x₂ β≈γ) = {!   !}
≈trans (V/ x x₁ α≈β) (V x₂ β≈γ) = V/ x x₁ (≈trans α≈β β≈γ)
≈trans (V/ x x₁ α≈β) (V/ x₂ x₃ β≈γ) = {!   !}

≈sym                  (atom r ts)  = atom r ts
≈sym                  (apα ⇒ apβ)  = ≈sym apα ⇒ ≈sym apβ
≈sym                  (apα ∧ apβ)  = ≈sym apα ∧ ≈sym apβ
≈sym                  (apα ∨ apβ)  = ≈sym apα ∨ ≈sym apβ
≈sym                  (Λ x ap)     = Λ x (≈sym ap)
≈sym {Λ x α} {Λ y α′} (Λ/ y∉α sub β≈β′) with varEq x y
... | yes refl rewrite subIdentFunc sub = Λ x (≈sym β≈β′)
... | no x≢y = ≈trans (Λ y (≈sym β≈β′)) (Λ/ (subNotFree (varterm x≢y) sub) (subInverse y∉α sub) ≈refl)
≈sym                  (V x ap)     = V x (≈sym ap)
≈sym {V x α} {V y α′} (V/ y∉α sub β≈β′) with varEq x y
... | yes refl rewrite subIdentFunc sub = V x (≈sym β≈β′)
... | no x≢y = ≈trans (V y (≈sym β≈β′)) (V/ (subNotFree (varterm x≢y) sub) (subInverse y∉α sub) ≈refl)

--≈notfree (atom r ts) (atom x) = atom x
--≈notfree (ap ⇒ ap₁) (x∉α ⇒ x∉α₁) = ≈notfree ap x∉α ⇒ ≈notfree ap₁ x∉α₁
--≈notfree (ap ∧ ap₁) (x∉α ∧ x∉α₁) = ≈notfree ap x∉α ∧ ≈notfree ap₁ x∉α₁
--≈notfree (ap ∨ ap₁) (x∉α ∨ x∉α₁) = ≈notfree ap x∉α ∨ ≈notfree ap₁ x∉α₁
--≈notfree (Λ x ap) (Λ∣ .x α) = Λ∣ x _
--≈notfree (Λ x ap) (Λ .x x∉α) = Λ x (≈notfree ap x∉α)
--≈notfree (Λ/ y∉α α[x/y]≡β) (Λ∣ x α) = {!   !}
--≈notfree (Λ/ x x₁) (Λ y x∉α) = {!   !}
--≈notfree (V x ap) (V∣ .x α) = V∣ x _
--≈notfree (V x ap) (V .x x∉α) = V x (≈notfree ap x∉α)
--≈notfree (V/ x x₁) (V∣ x₂ α) = {!   !}
--≈notfree (V/ x x₁) (V y x∉α) = {!   !}
--
--
--≈trans : ∀{α β γ} → α ≈ β → β ≈ γ → α ≈ γ
--≈trans (atom r ts) (atom .r .ts) = atom r ts
--≈trans (α₁≈β₁ ⇒ α₂≈β₂) (β₁≈γ₁ ⇒ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ⇒ ≈trans α₂≈β₂ β₂≈γ₂
--≈trans (α₁≈β₁ ∧ α₂≈β₂) (β₁≈γ₁ ∧ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ∧ ≈trans α₂≈β₂ β₂≈γ₂
--≈trans (α₁≈β₁ ∨ α₂≈β₂) (β₁≈γ₁ ∨ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ∨ ≈trans α₂≈β₂ β₂≈γ₂
--≈trans (Λ x α≈β) (Λ .x β≈γ) = Λ x (≈trans α≈β β≈γ)
--≈trans (Λ x α≈α′) (Λ/ y∉α′ α′[x/y]≡β) = Λ/ (≈notfree (≈sym α≈α′) y∉α′) {!   !}
--≈trans (Λ/ x x₁) (Λ x₂ x₃) = {!   !}
--≈trans (Λ/ x x₁) (Λ/ x₂ x₃) = {!   !}
--≈trans (V x α≈β) (V .x β≈γ) = V x (≈trans α≈β β≈γ)
--≈trans (V x x₁) (V/ x₂ x₃) = {!   !}
--≈trans (V/ x x₁) (V x₂ x₃) = {!   !}
--≈trans (V/ x x₁) (V/ x₂ x₃) = {!   !}


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
    x∉y : x NotFreeInTerm (varterm y)
    x∉y = varterm λ { refl → ¬x∉α (freshNotFree (snd yfr)) }
    βsub : Σ Formula (α [ x / varterm y ]≡_)
    βsub = α [ x / freshFreeFor (snd yfr) x ]
    β : Formula
    β = fst βsub
    α[x/y]≡β : α [ x / varterm y ]≡ β
    α[x/y]≡β = snd βsub
