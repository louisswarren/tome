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

≈sub : ∀{α α′ β β′ x t} → α ≈ α′ → α [ x / t ]≡ β → α′ [ x / t ]≡ β′ → β ≈ β′
≈sub ap (ident α x) sub₂ rewrite subIdentFunc sub₂ = ap
≈sub ap (notfree x∉α) sub₂ with subNotFreeFunc sub₂ (≈notfree ap x∉α)
... | refl = ap
≈sub ap sub₁ (ident α x) rewrite subIdentFunc sub₁ = ap
≈sub ap sub₁ (notfree x∉α′) with subNotFreeFunc sub₁ (≈notfree (≈sym ap) x∉α′)
... | refl = ap
≈sub (atom r ts) (atom .r x) (atom .r x₁) = {!   !}
≈sub (ap ⇒ ap₁) (sub₁ ⇒ sub₂) (sub₃ ⇒ sub₄) = ≈sub ap sub₁ sub₃ ⇒ ≈sub ap₁ sub₂ sub₄
≈sub (ap ∧ ap₁) (sub₁ ∧ sub₂) (sub₃ ∧ sub₄) = ≈sub ap sub₁ sub₃ ∧ ≈sub ap₁ sub₂ sub₄
≈sub (ap ∨ ap₁) (sub₁ ∨ sub₂) (sub₃ ∨ sub₄) = ≈sub ap sub₁ sub₃ ∨ ≈sub ap₁ sub₂ sub₄
≈sub (Λ x ap) (Λ∣ .x α) (Λ∣ .x α₁) = Λ x ap
≈sub (Λ x ap) (Λ∣ .x α) (Λ x₁ x₂ sub₂) = ⊥-elim (x₁ refl)
≈sub (Λ x ap) (Λ x₁ x₂ sub₁) (Λ∣ .x α) = ⊥-elim (x₁ refl)
≈sub (Λ x ap) (Λ x₁ x₂ sub₁) (Λ x₃ x₄ sub₂) = Λ x (≈sub ap sub₁ sub₂)
≈sub (Λ/ x x₁ ap) (Λ∣ x₂ α) (Λ∣ .x₂ α₁) = Λ/ x x₁ ap
≈sub (Λ/ x x₁ ap) (Λ∣ x₂ α) (Λ x₃ x₄ sub₂) with subNotFreeFunc sub₂ (≈notfree ap (subNotFree (varterm x₃) x₁))
...                                        | refl = Λ/ x x₁ ap
≈sub (Λ/ y∉α α[x/y]≡β ap) (Λ y≢x x₃ sub₁) (Λ∣ x₄ α) with subNotFreeFunc sub₁ y∉α
≈sub (Λ/ y∉α α[x/y]≡β ap) (Λ y≢x x₃ sub₁) (Λ∣ x₄ α) | refl = Λ/ y∉α α[x/y]≡β ap
≈sub (Λ/ y∉α α[x/y]≡β ap) (Λ x₂ x₃ sub₁) (Λ x₄ x₅ sub₂) = Λ/ {!   !} {!   !} (≈sub ap {!   !} sub₂)
≈sub (Λ/′ ap x x₁) (Λ∣ x₂ α) (Λ∣ .x₂ α₁) = Λ/′ ap x x₁
≈sub (Λ/′ ap x x₁) (Λ∣ x₂ α) (Λ x₃ x₄ sub₂) = {!   !}
≈sub (Λ/′ ap x x₁) (Λ x₂ x₃ sub₁) (Λ∣ x₄ α) = Λ/′ (≈sub ap sub₁ (notfree x)) x x₁
≈sub (Λ/′ ap x x₁) (Λ x₂ x₃ sub₁) (Λ x₄ x₅ sub₂) = {!   !}
≈sub (V x ap) sub₁ sub₂ = {! sub₁ sub₂  !}
≈sub (V/ x x₁ ap) sub₁ sub₂ = {!  sub₁ sub₂ !}
≈sub (V/′ ap x x₁) sub₁ sub₂ = {! sub₁ sub₂  !}






--≈trans : ∀{α₁ α₂ α₃} → α₁ ≈ α₂ → α₂ ≈ α₃ → α₁ ≈ α₃
--≈trans (atom r ts) (atom .r .ts) = atom r ts
--≈trans (α₁≈α₂ ⇒ β₁≈β₂) (α₂≈α₃ ⇒ β₂≈β₃) = ≈trans α₁≈α₂ α₂≈α₃ ⇒ ≈trans β₁≈β₂ β₂≈β₃
--≈trans (α₁≈α₂ ∧ β₁≈β₂) (α₂≈α₃ ∧ β₂≈β₃) = ≈trans α₁≈α₂ α₂≈α₃ ∧ ≈trans β₁≈β₂ β₂≈β₃
--≈trans (α₁≈α₂ ∨ β₁≈β₂) (α₂≈α₃ ∨ β₂≈β₃) = ≈trans α₁≈α₂ α₂≈α₃ ∨ ≈trans β₁≈β₂ β₂≈β₃
--≈trans (Λ x α₁≈α₂) (Λ .x α₂≈α₃) = Λ x (≈trans α₁≈α₂ α₂≈α₃)
--≈trans (Λ x α₁≈α₂) (Λ/ y∉α₂ α₂[x/y]≡β β≈α₃) = {!   !}
--≈trans (Λ x α₁≈α₂) (Λ/′ ap₂ x₁ x₂) = {!   !}
--≈trans (Λ/ x x₁ ap₁) ap₂ = {!   !}
--≈trans (Λ/′ ap₁ x x₁) ap₂ = {!   !}
--≈trans (V x ap₁) ap₂ = {!   !}
--≈trans (V/ x x₁ ap₁) ap₂ = {!   !}
--≈trans (V/′ ap₁ x x₁) ap₂ = {!   !}


--⟨←⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′)) d =
--  close
--   (assembled-context d)
--   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
--   (arrowelim
--    (arrowintro (Λ y β′)
--     (univintro x all⟨ x∉∀yβ′ ⟩ -- Only difference
--      (⟨←⟩ (renameIff α≈α′)
--       (univelim (varterm x) (subInverse y∉α′ α′[x/y]≡β′)
--        (assume (Λ y β′))))))
--    d)
--   where
--    x∉∀yβ′ : x NotFreeIn Λ y β′
--    x∉∀yβ′ with varEq x y
--    ...    | yes refl rewrite subIdentFunc α′[x/y]≡β′ = Λ∣ x β′
--    ...    | no  x≢y  = Λ y (subNotFree (varterm x≢y) α′[x/y]≡β′)
