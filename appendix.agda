open import Agda.Builtin.Sigma

open import Decidable
open import Formula
open import Nat
open import Vec

-- Prove that ident is a derived rule. Note that this proof does not make use
-- of Formula.ident
derived-ident : ∀ α x → α [ x / varterm x ]≡ α
derived-ident (atom r ts) x = atom r (identTerms ts x)
  where
    identTerms : ∀{n} → (ts : Vec Term n) → ∀ x → [ ts ][ x / varterm x ]≡ ts
    identTerms [] x = []
    identTerms (varterm y ∷ ts) x with varEq x y
    ...                           | yes refl = varterm≡ ∷ identTerms ts x
    ...                           | no  x≢y  = varterm≢ x≢y ∷ identTerms ts x
    identTerms (functerm f us ∷ ts) x = functerm (identTerms us x) ∷ identTerms ts x
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
                                                   ¬tff (Λ .α .y _ tffα) = ¬tffα tffα
    ...                             | yes tffα with y notFreeInTerm t
    ...                                        | yes ynft = yes (Λ α y ynft tffα)
    ...                                        | no ¬ynft = no ¬tff
                                                            where
                                                              ¬tff : _
                                                              ¬tff (notfree xnf) = xf xnf
                                                              ¬tff (Λ∣ .α) = x≢y refl
                                                              ¬tff (Λ .α .y ynft _) = ¬ynft ynft
    lemma (V y α)     xf with varEq x y
    ...                  | yes refl = yes (V∣ α)
    ...                  | no  x≢y  with t freeFor x In α
    ...                             | no ¬tffα = no ¬tff
                                                 where
                                                   ¬tff : _
                                                   ¬tff (notfree xnf) = xf xnf
                                                   ¬tff (V∣ .α) = x≢y refl
                                                   ¬tff (V .α .y _ tffα) = ¬tffα tffα
    ...                             | yes tffα with y notFreeInTerm t
    ...                                        | yes ynft = yes (V α y ynft tffα)
    ...                                        | no ¬ynft = no ¬tff
                                                            where
                                                              ¬tff : _
                                                              ¬tff (notfree xnf) = xf xnf
                                                              ¬tff (V∣ .α) = x≢y refl
                                                              ¬tff (V .α .y ynft _) = ¬ynft ynft

-- Generating not-free variables
supFreeTerm : ∀ t → Σ ℕ λ ⌈t⌉ → ∀ n → ⌈t⌉ < n → var n NotFreeInTerm t
supFreeTerm t with supFreeTerms (t ∷ [])
supFreeTerm t | s , pfs = s , notFreeIss
  where
    notFreeIss : ∀ n → s < n → var n NotFreeInTerm t
    notFreeIss n s<n with pfs n s<n
    notFreeIss n s<n | pf ∷ [] = pf


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

-- We have proved that if t is free for x in α then α [ x / t ] exists. The
-- converse is also true, meaning _FreeFor_In_ precisely captures the notion of
-- a substitution being possible.
subFreeFor : ∀{α x t β} → α [ x / t ]≡ β → t FreeFor x In α
subFreeFor (ident (atom r ts) x) = atom r ts
subFreeFor (ident (α ⇒ α₁) x) = subFreeFor (ident α x) ⇒ subFreeFor (ident α₁ x)
subFreeFor (ident (α ∧ α₁) x) = subFreeFor (ident α x) ∧ subFreeFor (ident α₁ x)
subFreeFor (ident (α ∨ α₁) x) = subFreeFor (ident α x) ∨ subFreeFor (ident α₁ x)
subFreeFor (ident (Λ x₁ α) x) with varEq x₁ x
subFreeFor (ident (Λ x₁ α) .x₁) | yes refl = Λ∣ α
subFreeFor (ident (Λ x₁ α) x) | no x₂ = Λ α x₁ (varterm x₂) (subFreeFor (ident α x))
subFreeFor (ident (V x₁ α) x) with varEq x₁ x
subFreeFor (ident (V x₁ α) .x₁) | yes refl = V∣ α
subFreeFor (ident (V x₁ α) x) | no x₂ = V α x₁ (varterm x₂) (subFreeFor (ident α x))
subFreeFor (notfree x) = notfree x
subFreeFor (atom r x) = atom r _
subFreeFor (rep ⇒ rep₁) = subFreeFor rep ⇒ subFreeFor rep₁
subFreeFor (rep ∧ rep₁) = subFreeFor rep ∧ subFreeFor rep₁
subFreeFor (rep ∨ rep₁) = subFreeFor rep ∨ subFreeFor rep₁
subFreeFor (Λ∣ x α) = Λ∣ α
subFreeFor (V∣ x α) = V∣ α
subFreeFor (Λ x x₁ rep) = Λ _ _ x₁ (subFreeFor rep)
subFreeFor (V x x₁ rep) = V _ _ x₁ (subFreeFor rep)


-- Show that substutution is functional
subUniqueTerms : ∀{n} → (us : Vec Term n) → ∀{x t} → {vs ws : Vec Term n} → [ us ][ x / t ]≡ vs → [ us ][ x / t ]≡ ws → vs ≡ ws
subUniqueTerms [] [] [] = refl
subUniqueTerms (varterm x ∷ us) (varterm≡ ∷ p) (varterm≡ ∷ q) with subUniqueTerms us p q
subUniqueTerms (varterm x ∷ us) (varterm≡ ∷ p) (varterm≡ ∷ q) | refl = refl
subUniqueTerms (varterm x ∷ us) (varterm≡ ∷ p) (varterm≢ x₁ ∷ q) = ⊥-elim (x₁ refl)
subUniqueTerms (varterm x ∷ us) (varterm≢ x₁ ∷ p) (varterm≡ ∷ q) = ⊥-elim (x₁ refl)
subUniqueTerms (varterm x ∷ us) (varterm≢ x₁ ∷ p) (varterm≢ x₂ ∷ q) with subUniqueTerms us p q
subUniqueTerms (varterm x ∷ us) (varterm≢ x₁ ∷ p) (varterm≢ x₂ ∷ q) | refl = refl
subUniqueTerms (functerm f ts ∷ us) (functerm x ∷ p) (functerm x₁ ∷ q) with subUniqueTerms ts x x₁ | subUniqueTerms us p q
subUniqueTerms (functerm f ts ∷ us) (functerm x ∷ p) (functerm x₁ ∷ q) | refl | refl = refl

subNotFreeIdentTerms : ∀{n x t} → (us : Vec Term n) → x NotFreeInTerms us → [ us ][ x / t ]≡ us
subNotFreeIdentTerms [] x = []
subNotFreeIdentTerms (varterm x₁ ∷ us) (varterm x ∷ x₂) = varterm≢ x ∷ subNotFreeIdentTerms us x₂
subNotFreeIdentTerms (functerm f ts ∷ us) (functerm x ∷ x₁) = functerm (subNotFreeIdentTerms ts x) ∷ subNotFreeIdentTerms us x₁

conotfree : ∀{α x t β} → α [ x / t ]≡ β → x NotFreeIn α → α ≡ β
conotfree (ident α x) x∉α = refl
conotfree (notfree x) x∉α = refl
conotfree (atom r x) x∉α = {!   !}
conotfree (subα ⇒ subβ) (x∉α ⇒ x∉β) with conotfree subα x∉α | conotfree subβ x∉β
...                                 | refl | refl = refl
conotfree (subα ∧ subβ) (x∉α ∧ x∉β) with conotfree subα x∉α | conotfree subβ x∉β
...                                 | refl | refl = refl
conotfree (subα ∨ subβ) (x∉α ∨ x∉β) with conotfree subα x∉α | conotfree subβ x∉β
...                                 | refl | refl = refl
conotfree (Λ∣ x α) _ = refl
conotfree (V∣ x α) _ = refl
conotfree (Λ x x₁ r) (Λ∣ x₂ α) = {!   !}
conotfree (Λ x x₁ r) (Λ y x∉α) = {!   !}
conotfree (V x x₁ r) x∉α = {!   !}

subUnique : ∀{x t α β γ} → α [ x / t ]≡ β → α [ x / t ]≡ γ → β ≡ γ
subUnique (ident α x) r = coident r
subUnique (notfree x∉α) r = conotfree r x∉α
subUnique r (ident α x) rewrite coident r = refl
subUnique r (notfree x∉α) rewrite conotfree r x∉α = refl
subUnique (atom r₁ x) r = {!   !}
subUnique (s ⇒ s₁) (r ⇒ r₁) = {!   !}
subUnique (s ∧ s₁) (r ∧ r₁) = {!   !}
subUnique (s ∨ s₁) (r ∨ r₁) = {!   !}
subUnique (Λ∣ x α) r = {!   !}
subUnique (V∣ x α) r = {!   !}
subUnique (Λ x x₁ s) r = {!   !}
subUnique (V x x₁ s) r = {!   !}

--subUnique : ∀ α → ∀{x t β γ} → α [ x / t ]≡ β → α [ x / t ]≡ γ → β ≡ γ
--subUnique _ (ident α x) q = coident q
--subUnique _ p (ident α x) = ≡sym (coident p)
--  where
--    ≡sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
--    ≡sym refl = refl
--subUnique (atom r ts) (notfree x) (notfree x₁) = refl
--subUnique (atom r ts) (notfree (atom x)) (atom .r x₁) with subUniqueTerms ts (subNotFreeIdentTerms ts x) x₁
--subUnique (atom r ts) (notfree (atom x)) (atom .r x₁) | refl = refl
--subUnique (atom r ts) (atom .r x) (notfree (atom x₁)) with subUniqueTerms ts (subNotFreeIdentTerms ts x₁) x
--subUnique (atom r ts) (atom .r x) (notfree (atom x₁)) | refl = refl
--subUnique (atom r ts) (atom .r x) (atom .r x₁) with subUniqueTerms ts x x₁
--subUnique (atom r ts) (atom .r x) (atom .r x₁) | refl = refl
--subUnique (α ⇒ β) (notfree (x₁ ⇒ x₂)) (notfree (y₁ ⇒ y₂)) = refl
--subUnique (α ⇒ β) (notfree (x₁ ⇒ x₂)) (q₁ ⇒ q₂) with subUnique α (notfree x₁) q₁ | subUnique β (notfree x₂) q₂
--subUnique (α ⇒ β) (notfree (x₁ ⇒ x₂)) (q₁ ⇒ q₂) | refl | refl = refl
--subUnique (α ⇒ β) (p₁ ⇒ p₂) (notfree (y₁ ⇒ y₂)) with subUnique α p₁ (notfree y₁) | subUnique β p₂ (notfree y₂)
--subUnique (α ⇒ β) (p₁ ⇒ p₂) (notfree (y₁ ⇒ y₂)) | refl | refl = refl
--subUnique (α ⇒ β) (p₁ ⇒ p₂) (q₁ ⇒ q₂)           with subUnique α p₁ q₁ | subUnique β p₂ q₂
--subUnique (α ⇒ β) (p₁ ⇒ p₂) (q₁ ⇒ q₂)           | refl | refl = refl
--subUnique (α ∧ β) (notfree (x₁ ∧ x₂)) (notfree (y₁ ∧ y₂)) = refl
--subUnique (α ∧ β) (notfree (x₁ ∧ x₂)) (q₁ ∧ q₂) with subUnique α (notfree x₁) q₁ | subUnique β (notfree x₂) q₂
--subUnique (α ∧ β) (notfree (x₁ ∧ x₂)) (q₁ ∧ q₂) | refl | refl = refl
--subUnique (α ∧ β) (p₁ ∧ p₂) (notfree (y₁ ∧ y₂)) with subUnique α p₁ (notfree y₁) | subUnique β p₂ (notfree y₂)
--subUnique (α ∧ β) (p₁ ∧ p₂) (notfree (y₁ ∧ y₂)) | refl | refl = refl
--subUnique (α ∧ β) (p₁ ∧ p₂) (q₁ ∧ q₂)           with subUnique α p₁ q₁ | subUnique β p₂ q₂
--subUnique (α ∧ β) (p₁ ∧ p₂) (q₁ ∧ q₂)           | refl | refl = refl
--subUnique (α ∨ β) (notfree (x₁ ∨ x₂)) (notfree (y₁ ∨ y₂)) = refl
--subUnique (α ∨ β) (notfree (x₁ ∨ x₂)) (q₁ ∨ q₂) with subUnique α (notfree x₁) q₁ | subUnique β (notfree x₂) q₂
--subUnique (α ∨ β) (notfree (x₁ ∨ x₂)) (q₁ ∨ q₂) | refl | refl = refl
--subUnique (α ∨ β) (p₁ ∨ p₂) (notfree (y₁ ∨ y₂)) with subUnique α p₁ (notfree y₁) | subUnique β p₂ (notfree y₂)
--subUnique (α ∨ β) (p₁ ∨ p₂) (notfree (y₁ ∨ y₂)) | refl | refl = refl
--subUnique (α ∨ β) (p₁ ∨ p₂) (q₁ ∨ q₂)           with subUnique α p₁ q₁ | subUnique β p₂ q₂
--subUnique (α ∨ β) (p₁ ∨ p₂) (q₁ ∨ q₂)           | refl | refl = refl
--subUnique (Λ x α) (notfree x₁) (notfree x₂) = refl
--subUnique (Λ x α) (notfree x₁) (Λ∣ .x .α) = refl
--subUnique (Λ x α) (notfree (Λ∣ .x .α)) (Λ x₂ x₃ q) = ⊥-elim (x₂ refl)
--subUnique (Λ x α) (notfree (Λ .x x₁)) (Λ x₂ x₃ q) with subUnique α (notfree x₁) q
--subUnique (Λ x α) (notfree (Λ .x x₁)) (Λ x₂ x₃ q) | refl = refl
--subUnique (Λ x α) (Λ∣ .x .α) (notfree x₁) = refl
--subUnique (Λ x α) (Λ∣ .x .α) (Λ∣ .x .α) = refl
--subUnique (Λ x α) (Λ∣ .x .α) (Λ x₁ x₂ q) = ⊥-elim (x₁ refl)
--subUnique (Λ x α) (Λ x₁ x₂ p) (notfree (Λ∣ .x .α)) = ⊥-elim (x₁ refl)
--subUnique (Λ x α) (Λ x₁ x₂ p) (notfree (Λ .x x₃)) with subUnique α p (notfree x₃)
--subUnique (Λ x α) (Λ x₁ x₂ p) (notfree (Λ .x x₃)) | refl = refl
--subUnique (Λ x α) (Λ x₁ x₂ p) (Λ∣ .x .α) = ⊥-elim (x₁ refl)
--subUnique (Λ x α) (Λ x₁ x₂ p) (Λ x₃ x₄ q) with subUnique α p q
--subUnique (Λ x α) (Λ x₁ x₂ p) (Λ x₃ x₄ q) | refl = refl
--subUnique (V x α) (notfree x₁) (notfree x₂) = refl
--subUnique (V x α) (notfree x₁) (V∣ .x .α) = refl
--subUnique (V x α) (notfree (V∣ .x .α)) (V x₂ x₃ q) = ⊥-elim (x₂ refl)
--subUnique (V x α) (notfree (V .x x₁)) (V x₂ x₃ q) with subUnique α (notfree x₁) q
--subUnique (V x α) (notfree (V .x x₁)) (V x₂ x₃ q) | refl = refl
--subUnique (V x α) (V∣ .x .α) (notfree x₁) = refl
--subUnique (V x α) (V∣ .x .α) (V∣ .x .α) = refl
--subUnique (V x α) (V∣ .x .α) (V x₁ x₂ q) = ⊥-elim (x₁ refl)
--subUnique (V x α) (V x₁ x₂ p) (notfree (V∣ .x .α)) = ⊥-elim (x₁ refl)
--subUnique (V x α) (V x₁ x₂ p) (notfree (V .x x₃)) with subUnique α p (notfree x₃)
--subUnique (V x α) (V x₁ x₂ p) (notfree (V .x x₃)) | refl = refl
--subUnique (V x α) (V x₁ x₂ p) (V∣ .x .α) = ⊥-elim (x₁ refl)
--subUnique (V x α) (V x₁ x₂ p) (V x₃ x₄ q) with subUnique α p q
--subUnique (V x α) (V x₁ x₂ p) (V x₃ x₄ q) | refl = refl



≈refl : ∀{α} → α ≈ α
≈refl {atom r ts} = atom r ts
≈refl {α ⇒ β} = ≈refl ⇒ ≈refl
≈refl {α ∧ β} = ≈refl ∧ ≈refl
≈refl {α ∨ β} = ≈refl ∨ ≈refl
≈refl {Λ x α} = Λ x ≈refl
≈refl {V x α} = V x ≈refl

--≈trans : ∀{α β γ} → α ≈ β → β ≈ γ → α ≈ γ
--≈trans (atom r ts) (atom .r .ts) = atom r ts
--≈trans (α₁≈β₁ ⇒ α₂≈β₂) (β₁≈γ₁ ⇒ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ⇒ ≈trans α₂≈β₂ β₂≈γ₂
--≈trans (α₁≈β₁ ∧ α₂≈β₂) (β₁≈γ₁ ∧ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ∧ ≈trans α₂≈β₂ β₂≈γ₂
--≈trans (α₁≈β₁ ∨ α₂≈β₂) (β₁≈γ₁ ∨ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ∨ ≈trans α₂≈β₂ β₂≈γ₂
--≈trans (Λ x α≈β) (Λ .x β≈γ) = Λ x (≈trans α≈β β≈γ)
--≈trans (Λ x x₁) (Λ/ x₂ x₃) = {!   !}
--≈trans (Λ/ x x₁) (Λ x₂ x₃) = {!   !}
--≈trans (Λ/ x x₁) (Λ/ x₂ x₃) = {!   !}
--≈trans (V x α≈β) (V .x β≈γ) = {!   !}
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

