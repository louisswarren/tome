
open import Decidable
open import Deduction
open import Ensemble
open import Formula
open import List
open import Vec

-- should allow different levels
record _↔_ {a} (A : Set a) (B : Set a) : Set a where
  field
    ⟨→⟩ : A → B
    ⟨←⟩ : B → A
open _↔_ 


infix 50 _≈_
data _≈_ : Formula → Formula → Set where
  atom : ∀ r ts → atom r ts ≈ atom r ts
  _⇒_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ⇒ β ≈ α′ ⇒ β′
  _∧_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ∧ β ≈ α′ ∧ β′
  _∨_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ∨ β ≈ α′ ∨ β′
  Λ    : ∀{α α′} → ∀ x → α ≈ α′ → Λ x α ≈ Λ x α′
  Λ/   : ∀{α β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β → β ≈ β′ → Λ x α ≈ Λ y β′
  Λ/′  : ∀{α α′ β′ x y} → α ≈ α′ → y NotFreeIn α′ → α′ [ x / varterm y ]≡ β′ → Λ x α ≈ Λ y β′
  V    : ∀{α α′} → ∀ x → α ≈ α′ → V x α ≈ V x α′
  V/   : ∀{α β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β → β ≈ β′ → V x α ≈ V y β′
  V/′  : ∀{α α′ β′ x y} → α ≈ α′ → y NotFreeIn α′ → α′ [ x / varterm y ]≡ β′ → V x α ≈ V y β′


≈refl : ∀{α} → α ≈ α
≈refl {atom r ts} = atom r ts
≈refl {α ⇒ β} = ≈refl ⇒ ≈refl
≈refl {α ∧ β} = ≈refl ∧ ≈refl
≈refl {α ∨ β} = ≈refl ∨ ≈refl
≈refl {Λ x α} = Λ x ≈refl
≈refl {V x α} = V x ≈refl


≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α
≈sym (atom r ts) = atom r ts
≈sym (α≈α′ ⇒ β≈β′) = ≈sym α≈α′ ⇒ ≈sym β≈β′
≈sym (α≈α′ ∧ β≈β′) = ≈sym α≈α′ ∧ ≈sym β≈β′
≈sym (α≈α′ ∨ β≈β′) = ≈sym α≈α′ ∨ ≈sym β≈β′
≈sym (Λ x α≈α′) = Λ x (≈sym α≈α′)
≈sym {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = Λ x (≈sym β≈β′)
...    | no x≢y = Λ/′ (≈sym β≈β′) (subNotFree (varterm x≢y) α[x/y]≡β) (subInverse y∉α α[x/y]≡β)
≈sym {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′) with varEq x y
...    | yes refl rewrite subIdentFunc α′[x/y]≡β′ = Λ x (≈sym α≈α′)
...    | no  x≢y  = Λ/ (subNotFree (varterm x≢y) α′[x/y]≡β′) (subInverse y∉α′ α′[x/y]≡β′) (≈sym α≈α′)
≈sym (V x α≈α′) = V x (≈sym α≈α′)
≈sym {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = V x (≈sym β≈β′)
...    | no x≢y = V/′ (≈sym β≈β′) (subNotFree (varterm x≢y) α[x/y]≡β) (subInverse y∉α α[x/y]≡β)
≈sym {V x α} {V y β′} (V/′ α≈α′ y∉α′ α′[x/y]≡β′) with varEq x y
...    | yes refl rewrite subIdentFunc α′[x/y]≡β′ = V x (≈sym α≈α′)
...    | no  x≢y  = V/ (subNotFree (varterm x≢y) α′[x/y]≡β′) (subInverse y∉α′ α′[x/y]≡β′) (≈sym α≈α′)


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
≈notfree {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′) (Λ∣ x α) with varEq x y
...    | yes refl = Λ∣ x β′
...    | no  x≢y  = Λ y (subNotFree (varterm x≢y) α′[x/y]≡β′)
≈notfree {V x α} {V y β′} (V/′ α≈α′ y∉α′ α′[x/y]≡β′) (V∣ x α) with varEq x y
...    | yes refl = V∣ x β′
...    | no  x≢y  = V y (subNotFree (varterm x≢y) α′[x/y]≡β′)
≈notfree (Λ y α≈α′) (Λ .y z∉α) = Λ y (≈notfree α≈α′ z∉α)
≈notfree (V y α≈α′) (V .y z∉α) = V y (≈notfree α≈α′ z∉α)
≈notfree {Λ x α} {Λ y β′} {z} (Λ/ y∉α α[x/y]≡β β≈β′) (Λ .x z∉α) with varEq z y
...    | yes refl = Λ∣ z β′
...    | no  z≢y  = Λ y (≈notfree β≈β′ (notfreeSub z∉α (varterm z≢y) α[x/y]≡β))
≈notfree {V x α} {V y β′} {z} (V/ y∉α α[x/y]≡β β≈β′) (V .x z∉α) with varEq z y
...    | yes refl = V∣ z β′
...    | no  z≢y  = V y (≈notfree β≈β′ (notfreeSub z∉α (varterm z≢y) α[x/y]≡β))
≈notfree {Λ x α} {Λ y β′} {z} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β) (Λ .x z∉α) with varEq z y
...    | yes refl = Λ∣ z β′
...    | no  z≢y  = Λ y (notfreeSub (≈notfree α≈α′ z∉α) (varterm z≢y) α′[x/y]≡β)
≈notfree {V x α} {V y β′} {z} (V/′ α≈α′ y∉α′ α′[x/y]≡β) (V .x z∉α) with varEq z y
...    | yes refl = V∣ z β′
...    | no  z≢y  = V y (notfreeSub (≈notfree α≈α′ z∉α) (varterm z≢y) α′[x/y]≡β)



rename : ∀{Γ α α′} → α ≈ α′ → (Γ ⊢ α) ↔ (Γ ⊢ α′)
⟨→⟩ (rename {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts)) d = d
⟨→⟩ (rename {Γ} {α ⇒ β} {α′ ⇒ β′} (apα ⇒ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂))
   (arrowintro α′
    (⟨→⟩ (rename apβ)
     (arrowelim
      d
      (⟨←⟩ (rename apα) -- Not structurally recursive
       (assume α′)))))
⟨→⟩ (rename {Γ} {α ∧ β} {α′ ∧ β′} (apα ∧ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ z₃))))
   (conjelim
    d
    (conjintro
     (⟨→⟩ (rename apα)
      (assume α))
     (⟨→⟩ (rename apβ)
      (assume β))))
⟨→⟩ (rename {Γ} {α ∨ β} {α′ ∨ β′} (apα ∨ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
   (disjelim
    d
    (disjintro₁ β′
     (⟨→⟩ (rename apα)
      (assume α)))
    (disjintro₂ α′
     (⟨→⟩ (rename apβ)
      (assume β))))
⟨→⟩ (rename {Γ} {Λ x α} {Λ .x α′} (Λ y ap)) d =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro x (all⟨ Λ∣ x α ⟩)
      (⟨→⟩ (rename ap)
       (univelim (varterm x) (ident α x)
        (assume (Λ x α))))))
    d)
⟨→⟩ (rename {Γ} {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′)) d =
  close
    (assembled-context d)
    (λ x₁ z → z (λ z₁ → z₁ (λ z₂ → z₂)))
    (arrowelim
     (arrowintro (Λ x α)
      (univintro y all⟨ Λ x y∉α ⟩
       (⟨→⟩ (rename β≈β′)
        (univelim (varterm y) α[x/y]≡β
         (assume (Λ x α))))))
     d)
⟨→⟩ (rename {Γ} {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β)) d =
  close
    (assembled-context d)
    (λ x₁ z → z (λ z₁ → z₁ (λ z₂ → z₂)))
    (arrowelim
     (arrowintro (Λ x α)
      (univintro y all⟨ ≈notfree (Λ x (≈sym α≈α′)) (Λ x y∉α′) ⟩
       (univelim (varterm y) α′[x/y]≡β
        (univintro x all⟨ Λ∣ x α ⟩
         (⟨→⟩ (rename α≈α′) -- Not structurally recursive
          (univelim (varterm x) (ident α x)
           (assume (Λ x α))))))))
     d)
⟨→⟩ (rename {Γ} {V x α} {V .x β} (V y ap)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) x (ident β x)
     (⟨→⟩ (rename ap)
      (assume α))))
⟨→⟩ (rename {Γ} {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′)) d with varEq x y
... | no  x≢y  =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ z₃ (λ z₅ → z₅ (λ z₆ → z₆)))))
   (existelim (all⟨ V y (≈notfree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β)) ⟩
               all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- all⟨- [ refl ] ⟩))))
    d
    (existelim (all⟨ V∣ y β′ ⟩ all∪ (all- all⟨- [ refl ] ⟩))
     (existintro (varterm x) y (subInverse y∉α α[x/y]≡β)
      (assume α))
     (existintro (varterm y) y (ident β′ y)
      (⟨→⟩ (rename β≈β′) -- Not structurally recursive
       (assume _)))))
... | yes refl with subIdentFunc α[x/y]≡β
...            | refl =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β′ ⟩ all∪ (all- all⟨ y∉α ⟩))
    d
    (existintro (varterm x) x (ident β′ x)
     (⟨→⟩ (rename β≈β′)
      (assume α))))
⟨→⟩ (rename {Γ} {V x α} {V y β} (V/′ α≈α′ y∉α′ α′[x/y]≡β)) d with varEq x y
... | yes refl rewrite subIdentFunc α′[x/y]≡β =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) x (ident β x)
     (⟨→⟩ (rename α≈α′) -- Not structurally recursive
      (assume α))))
... | no x≢y   =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V y (subNotFree (varterm x≢y) α′[x/y]≡β) ⟩
               all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) y (subInverse y∉α′ α′[x/y]≡β)
     (⟨→⟩ (rename α≈α′)
      (assume α))))

⟨←⟩ (rename {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts)) d = d
⟨←⟩ (rename {Γ} {α ⇒ β} {α′ ⇒ β′} (apα ⇒ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂))
   (arrowintro α
    (⟨←⟩ (rename apβ)
     (arrowelim
      d
      (⟨→⟩ (rename apα) -- Not structurally recursive
       (assume α)))))
⟨←⟩ (rename {Γ} {α ∧ β} {α′ ∧ β′} (apα ∧ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ z₃))))
   (conjelim
    d
    (conjintro
     (⟨←⟩ (rename apα)
      (assume α′))
     (⟨←⟩ (rename apβ)
      (assume β′))))
⟨←⟩ (rename {Γ} {α ∨ β} {α′ ∨ β′} (apα ∨ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
   (disjelim
    d
    (disjintro₁ β
     (⟨←⟩ (rename apα)
      (assume α′)))
    (disjintro₂ α
     (⟨←⟩ (rename apβ)
      (assume β′))))
⟨←⟩ (rename {Γ} {Λ x α} {Λ .x α′} (Λ y ap)) d =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α′)
     (univintro x (all⟨ Λ∣ x α′ ⟩)
      (⟨←⟩ (rename ap)
       (univelim (varterm x) (ident α′ x)
        (assume (Λ x α′))))))
    d)
⟨←⟩ (rename {Γ} {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′)) d with varEq x y
... | yes refl = ?
... | no  x≢y  =
  close
    (assembled-context d)
    (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
    (arrowelim
     (arrowintro (Λ y β′)
      (univintro x all⟨ Λ y (≈notfree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β)) ⟩ (univelim (varterm x) (subInverse y∉α α[x/y]≡β) (univintro y all⟨ Λ∣ y β′ ⟩ (⟨←⟩ (rename β≈β′) (univelim (varterm y) (ident β′ y) (assume (Λ y β′))))))))
     d)
⟨←⟩ (rename {Γ} {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β)) d =
  close
    (assembled-context d)
    ? --(λ x₁ z → z (λ z₁ → z₁ (λ z₂ → z₂)))
    (arrowelim
     (arrowintro (Λ y β′)
      ?)
      --(univintro y all⟨ ≈notfree (Λ x (≈sym α≈α′)) (Λ x y∉α′) ⟩
      -- (univelim (varterm y) α′[x/y]≡β
      --  (univintro x all⟨ Λ∣ x α ⟩
      --   (⟨←⟩ (rename α≈α′) -- Not structurally recursive
      --    (univelim (varterm x) (ident α x)
      --     (assume (Λ x α))))))))
     d)
⟨←⟩ (rename {Γ} {V x α} {V .x β} (V y ap)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) x (ident α x)
     (⟨←⟩ (rename ap)
      (assume β))))
⟨←⟩ (rename {Γ} {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′)) d with varEq x y
... | no  x≢y  =
  close
   (assembled-context d)
   ?
   ?
   --(λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ z₃ (λ z₅ → z₅ (λ z₆ → z₆)))))
   --(existelim (all⟨ V y (≈notfree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β)) ⟩
   --            all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- all⟨- [ refl ] ⟩))))
   -- d
   -- (existelim (all⟨ V∣ y β′ ⟩ all∪ (all- all⟨- [ refl ] ⟩))
   --  (existintro (varterm x) y (subInverse y∉α α[x/y]≡β)
   --   (assume α))
   --  (existintro (varterm y) y (ident β′ y)
   --   (⟨←⟩ (rename β≈β′) -- Not structurally recursive
   --    (assume _)))))
... | yes refl with subIdentFunc α[x/y]≡β
...            | refl =
  close
   (assembled-context d)
   ?
   ?
   --(λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   --(existelim (all⟨ V∣ x β′ ⟩ all∪ (all- all⟨ y∉α ⟩))
   -- d
   -- (existintro (varterm x) x (ident β′ x)
   --  (⟨←⟩ (rename β≈β′)
   --   (assume α))))
⟨←⟩ (rename {Γ} {V x α} {V y β} (V/′ α≈α′ y∉α′ α′[x/y]≡β)) d with varEq x y
... | yes refl rewrite subIdentFunc α′[x/y]≡β =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) x (ident α x)
     (⟨←⟩ (rename α≈α′) -- Not structurally recursive
      (assume β))))
... | no x≢y   =
  close
   (assembled-context d)
   ?
   ?
   --(λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   --(existelim (all⟨ V y (subNotFree (varterm x≢y) α′[x/y]≡β) ⟩
   --            all∪ (all- all⟨- [ refl ] ⟩))
   -- d
   -- (existintro (varterm x) y (subInverse y∉α′ α′[x/y]≡β)
   --  (⟨←⟩ (rename α≈α′)
   --   (assume α))))

