open import Agda.Builtin.String

open import Formula hiding (_∷_)
open import Menge
open import Deduction hiding (rename)

postulate ≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α

rename      : ∀{Γ α α′}
              → α ≈ α′
              →                                Γ ⊢ α
                                              --------
              →                                Γ ⊢ α′
rename {Γ} {atom r ts} {.(atom r ts)} refl d = d
rename {Γ} {α ⇒ β} {.(α ⇒ β)} refl d = d
rename {Γ} {α ⇒ β} {α′ ⇒ β′} (apα ⇒ apβ) d = close (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ (λ z₄ → z₄ z₂ (λ z₅ → z₅)))) (arrowintro α′ (rename apβ (arrowelim d (rename (≈sym apα) (assume α′)))))
rename {Γ} {α ∧ α₁} {.(α ∧ α₁)} refl d = d
rename {Γ} {α ∧ α₁} {.(_ ∧ _)} (ap ∧ ap₁) d = {!   !}
rename {Γ} {α ∨ α₁} {.(α ∨ α₁)} refl d = d
rename {Γ} {α ∨ α₁} {.(_ ∨ _)} (ap ∨ ap₁) d = {!   !}
rename {Γ} {Λ x α} {.(Λ x α)} refl d = d
rename {Γ} {Λ x α} {.(Λ x _)} (Λ ap) d = {!   !}
rename {Γ} {Λ x α} {.(Λ _ _)} (Λ/ β x₁ x₂ ap) d = {!   !}
rename {Γ} {V x α} {.(V x α)} refl d = d
rename {Γ} {V x α} {.(V x _)} (V ap) d = {!   !}
rename {Γ} {V x α} {.(V _ _)} (V/ β x₁ x₂ ap) d = {!   !}
