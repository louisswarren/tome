open import Agda.Builtin.String

import List
open import Decidable
open import Formula hiding (_∷_)
open import Ensemble
open import Deduction hiding (rename)

open import appendix

≈refl : ∀{α} → α ≈ α
≈refl {atom r ts} = atom r ts
≈refl {α ⇒ β} = ≈refl ⇒ ≈refl
≈refl {α ∧ β} = ≈refl ∧ ≈refl
≈refl {α ∨ β} = ≈refl ∨ ≈refl
≈refl {Λ x α} = Λ x ≈refl
≈refl {V x α} = V x ≈refl

≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α
≈sym                  (atom r ts)  = atom r ts
≈sym                  (apα ⇒ apβ)  = ≈sym apα ⇒ ≈sym apβ
≈sym                  (apα ∧ apβ)  = ≈sym apα ∧ ≈sym apβ
≈sym                  (apα ∨ apβ)  = ≈sym apα ∨ ≈sym apβ
≈sym                  (Λ x ap)     = Λ x (≈sym ap)
≈sym {Λ x α} {Λ y α′} (Λ/ y∉α sub) with varEq x y
... | yes refl rewrite subUnique α sub (ident α x) = Λ x ≈refl
... | no x≢y = Λ/ (subNotFree (varterm x≢y) sub) (subInverse y∉α sub)
≈sym                  (V x ap)     = V x (≈sym ap)
≈sym {V x α} {V y α′} (V/ y∉α sub) with varEq x y
... | yes refl rewrite subUnique α sub (ident α x) = V x ≈refl
... | no x≢y = V/ (subNotFree (varterm x≢y) sub) (subInverse y∉α sub)


≈trans : ∀{α β γ} → α ≈ β → β ≈ γ → α ≈ γ
≈trans (atom r ts) (atom .r .ts) = atom r ts
≈trans (α₁≈β₁ ⇒ α₂≈β₂) (β₁≈γ₁ ⇒ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ⇒ ≈trans α₂≈β₂ β₂≈γ₂
≈trans (α₁≈β₁ ∧ α₂≈β₂) (β₁≈γ₁ ∧ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ∧ ≈trans α₂≈β₂ β₂≈γ₂
≈trans (α₁≈β₁ ∨ α₂≈β₂) (β₁≈γ₁ ∨ β₂≈γ₂) = ≈trans α₁≈β₁ β₁≈γ₁ ∨ ≈trans α₂≈β₂ β₂≈γ₂
≈trans (Λ x α≈β) (Λ .x β≈γ) = Λ x (≈trans α≈β β≈γ)
≈trans (Λ x x₁) (Λ/ x₂ x₃) = {!   !}
≈trans (Λ/ x x₁) (Λ x₂ x₃) = {!   !}
≈trans (Λ/ x x₁) (Λ/ x₂ x₃) = {!   !}
≈trans (V x α≈β) (V .x β≈γ) = {!   !}
≈trans (V x x₁) (V/ x₂ x₃) = {!   !}
≈trans (V/ x x₁) (V x₂ x₃) = {!   !}
≈trans (V/ x x₁) (V/ x₂ x₃) = {!   !}


rename      : ∀{Γ α α′}
              → α ≈ α′
              →                                Γ ⊢ α
                                              --------
              →                                Γ ⊢ α′
rename {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts) d = d
rename {Γ} {α ⇒ β} {α′ ⇒ β′} (apα ⇒ apβ) d =
  close
   (dm⊢ d)
   (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂))
   (arrowintro α′
    (rename apβ
     (arrowelim
      d
      (rename (≈sym apα)
       (assume α′)))))
rename {Γ} {α ∧ β} {α′ ∧ β′} (apα ∧ apβ) d =
  close
   (dm⊢ d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ z₃))))
   (conjelim
    d
    (conjintro
     (rename apα
      (assume α))
     (rename apβ
      (assume β))))
rename {Γ} {α ∨ β} {α′ ∨ β′} (apα ∨ apβ) d =
  close
   (dm⊢ d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
   (disjelim
    d
    (disjintro₁ β′
     (rename apα
      (assume α)))
    (disjintro₂ α′
     (rename apβ
      (assume β))))
rename {Γ} {Λ x α} {Λ .x α′} (Λ y ap) d =
  close
   (dm⊢ d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro x (all⟨ Λ∣ x α ⟩)
      (rename ap
       (univelim (varterm x) (ident α x)
        (assume (Λ x α))))))
    d)
rename {Γ} {Λ x α} {Λ y β} (Λ/ y∉α sub) d =
  close
   (dm⊢ d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro y (all⟨ Λ x y∉α ⟩)
      (univelim (varterm y) sub
       (assume (Λ x α)))))
    d)
rename {Γ} {V x α} {V .x β} (V y ap) d =
  close
   (dm⊢ d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β ⟩ all∪ (α all~ (all- List.[ refl ])))
    d
    (existintro (varterm x) x (ident β x)
     (rename ap
      (assume α))))
rename {Γ} {V x α} {V y β} (V/ y∉α sub) d with varEq x y
... | yes refl rewrite subUnique α sub (ident α x) = d
... | no x≢y   = close
                  (dm⊢ d)
                  (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
                  (existelim (all⟨ V y (subNotFree (varterm x≢y) sub) ⟩
                              all∪ (α all~ (all- List.[ refl ])))
                   d
                   (existintro (varterm x) y (subInverse y∉α sub)
                    (assume α)))
