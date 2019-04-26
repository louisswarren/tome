open import Agda.Builtin.String

import List
open import Decidable
open import Formula hiding (_∷_)
open import Menge
open import Deduction hiding (rename)

open import appendix

≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α
≈sym                  refl         = refl
≈sym                  (apα ⇒ apβ)  = ≈sym apα ⇒ ≈sym apβ
≈sym                  (apα ∧ apβ)  = ≈sym apα ∧ ≈sym apβ
≈sym                  (apα ∨ apβ)  = ≈sym apα ∨ ≈sym apβ
≈sym                  (Λ ap)       = Λ (≈sym ap)
≈sym {Λ x α} {Λ y α′} (Λ/ y∉α sub) with varEq x y
... | yes refl rewrite subUnique α sub (ident α x) = Λ refl
... | no x≢y = Λ/ (subNotFree (varterm x≢y) sub) (subInverse y∉α sub)
≈sym                  (V ap)       = V (≈sym ap)
≈sym {V x α} {V y α′} (V/ y∉α sub) with varEq x y
... | yes refl rewrite subUnique α sub (ident α x) = V refl
... | no x≢y = V/ (subNotFree (varterm x≢y) sub) (subInverse y∉α sub)


--≈trans : ∀{α β γ} → α ≈ β → β ≈ γ → α ≈ γ
--≈trans refl x₁ = x₁
--≈trans x₁ refl = x₁
--≈trans (x ⇒ x₂) (x₁ ⇒ x₃) = ≈trans x x₁ ⇒ ≈trans x₂ x₃
--≈trans (x ∧ x₂) (x₁ ∧ x₃) = ≈trans x x₁ ∧ ≈trans x₂ x₃
--≈trans (x ∨ x₂) (x₁ ∨ x₃) = ≈trans x x₁ ∨ ≈trans x₂ x₃
--≈trans (Λ x) (Λ x₁) = Λ (≈trans x x₁)
--≈trans (Λ α≈α′) (Λ/ y∉α′ sub) = {!   !}
--≈trans (Λ/ x x₂) (Λ x₁) = {!   !}
--≈trans (Λ/ x x₂) (Λ/ x₁ x₃) = {!   !}
--≈trans (V x) (V x₁) = V (≈trans x x₁)
--≈trans (V x) (V/ x₁ x₂) = {!   !}
--≈trans (V/ x x₂) (V x₁) = {!   !}
--≈trans (V/ x x₂) (V/ x₁ x₃) = {!   !}

rename      : ∀{Γ α α′}
              → α ≈ α′
              →                                Γ ⊢ α
                                              --------
              →                                Γ ⊢ α′
rename {Γ} {atom r ts} {.(atom r ts)} refl d = d
rename {Γ} {α ⇒ β} {.(α ⇒ β)} refl d = d
rename {Γ} {α ⇒ β} {α′ ⇒ β′} (apα ⇒ apβ) d = close (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ (λ z₄ → z₄ z₂ (λ z₅ → z₅)))) (arrowintro α′ (rename apβ (arrowelim d (rename (≈sym apα) (assume α′)))))
rename {Γ} {α ∧ β} {.(α ∧ β)} refl d = d
rename {Γ} {α ∧ β} {α′ ∧ β′} (apα ∧ apβ) d = close (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ → z₇ z₅ (λ z₈ → z₈)) (λ z₇ → z₇ z₃ (λ z₈ → z₈)))))) (conjelim d (conjintro (rename apα (assume α)) (rename apβ (assume β))))
rename {Γ} {α ∨ β} {.(α ∨ β)} refl d = d
rename {Γ} {α ∨ β} {α′ ∨ β′} (apα ∨ apβ) d = close (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄ (λ z₆ → z₆))) (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄ (λ z₆ → z₆))))) (disjelim d (disjintro₁ β′ (rename apα (assume α))) (disjintro₂ α′ (rename apβ (assume β))))
rename {Γ} {Λ x α} {.(Λ x α)} refl d = d
rename {Γ} {Λ x α} {Λ .x α′} (Λ ap) d = close (λ x z → z (λ z₁ → z₁ (λ z₂ z₃ → z₃ z₂ (λ z₄ → z₄)))) (arrowelim (arrowintro (Λ x α) (univintro x (Λ∣ x α all∷ all∅) (rename ap (univelim (varterm x) (ident α x) (assume (Λ x α)))))) d)
rename {Γ} {Λ x α} {Λ y β} (Λ/ y∉α sub) d = close (λ x z → z (λ z₁ → z₁ (λ z₂ z₃ → z₃ z₂ (λ z₄ → z₄)))) (arrowelim (arrowintro (Λ x α) (univintro y (Λ x y∉α all∷ all∅) (univelim (varterm y) sub (assume (Λ x α))))) d)
rename {Γ} {V x α} {.(V x α)} refl d = d
rename {Γ} {V x α} {V .x β} (V ap) d = close (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ z₃ (λ z₅ → z₅)))) (existelim (V∣ x β all∷ (α all~ (List.[ refl ] all-∷ all∅))) d (existintro (varterm x) x (ident β x) (rename ap (assume α))))
rename {Γ} {V x α} {V y β} (V/ y∉α sub) d with varEq x y
... | yes refl rewrite subUnique α sub (ident α x) = d
... | no x≢y   = close (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ z₃ (λ z₅ → z₅)))) (existelim (V y (subNotFree (varterm x≢y) sub) all∷ (α all~ (List.[ refl ] all-∷ all∅))) d (existintro (varterm x) y (subInverse y∉α sub) (assume α)))
