\begin{code}

module Deduction where

open import Agda.Builtin.String

open import Decidable
open import Ensemble
open import Formula
open import List

private
  _NotFreeInAll_ : Variable → Pred Formula → Set₁
  x NotFreeInAll Γ = Ensemble.All (x NotFreeIn_) Γ

infix 1 _⊢_ ⊢_
data _⊢_ : Pred Formula → Formula → Set₁ where

\end{code}
The first constructor is used for typesetting later; a deduction can be
abbreviated to a label. This will be used for lemmas, and for applying assumed
axiom schemes.
\begin{code}

  cite        : ∀{α} → String → ∅ ⊢ α → ∅ ⊢ α

\end{code}
The following constructor exists for two reasons:
\begin{enumerate}
  \item If $\Gamma \vdash \alpha$ then $\Gamma, \beta \vdash \alpha$
  \item We want to be able to normalise $\Gamma$, for example from $\{\alpha\}
    \setminus \alpha$ to $\emptyset$.
\end{enumerate}
\begin{code}

  close       : ∀{Γ Δ α} → Assembled formulaEq Δ → Γ ⊂ Δ → Γ ⊢ α → Δ ⊢ α

\end{code}
The remaining constructors correspond to the usual natural deduction rules.
Agda's comment syntax (\inline{--}) allows these rules to be formatted as
Gentzen style inferences.
\begin{code}

  assume      : (α : Formula)
                →                              ⟨ α ⟩ ⊢ α

  arrowintro  : ∀{Γ β} → (α : Formula)
                →                                  Γ ⊢ β
                                              --------------- ⇒⁺ α
                →                              Γ - α ⊢ α ⇒ β

  arrowelim   : ∀{Γ₁ Γ₂ α β}
                →                          Γ₁ ⊢ α ⇒ β    →    Γ₂ ⊢ α
                                          --------------------------- ⇒⁻
                →                                 Γ₁ ∪ Γ₂ ⊢ β

  conjintro   : ∀{Γ₁ Γ₂ α β}
                →                           Γ₁ ⊢ α    →    Γ₂ ⊢ β
                                           ----------------------- ∧⁺
                →                              Γ₁ ∪ Γ₂ ⊢ α ∧ β

  conjelim    : ∀{Γ₁ Γ₂ α β γ}
                →                         Γ₁ ⊢ α ∧ β    →    Γ₂ ⊢ γ
                                         --------------------------- ∧⁻
                →                           Γ₁ ∪ (Γ₂ - α - β) ⊢ γ

  disjintro₁  : ∀{Γ α} → (β : Formula)
                →                                   Γ ⊢ α
                                                 ----------- ∨⁺₁
                →                                 Γ ⊢ α ∨ β

  disjintro₂  : ∀{Γ β} → (α : Formula)
                →                                   Γ ⊢ β
                                                 ----------- ∨⁺₂
                →                                 Γ ⊢ α ∨ β

  disjelim    : ∀{Γ₁ Γ₂ Γ₃ α β γ}
                →             Γ₁ ⊢ α ∨ β    →    Γ₂ ⊢ γ    →    Γ₃ ⊢ γ
                             ------------------------------------------ ∨⁻
                →                   Γ₁ ∪ (Γ₂ - α) ∪ (Γ₃ - β) ⊢ γ

\end{code}
The constructors for first order logic require an extra proof to be supplied,
either of variable boundedness or variable replacement. The propositions proved
here have been formulated so that Agda's built-in proof search should be able to
supply them.
\begin{code}

  univintro   : ∀{Γ α} → (x : Variable)
                → x NotFreeInAll Γ
                →                                   Γ ⊢ α
                                                 ----------- ∀⁺
                →                                 Γ ⊢ Λ x α

  univelim    : ∀{Γ α x α[x/r]} → (r : Term)
                → α [ x / r ]≡ α[x/r]
                →                                Γ ⊢ Λ x α
                                                ------------ ∀⁻
                →                                Γ ⊢ α[x/r]

  existintro  : ∀{Γ α α[x/r]} → (r : Term) → (x : Variable)
                → α [ x / r ]≡ α[x/r]
                →                                Γ ⊢ α[x/r]
                                                ------------ ∃⁺
                →                                Γ ⊢ V x α

  existelim   : ∀{Γ₁ Γ₂ α β x}
                → x NotFreeInAll (⟨ β ⟩ ∪ (Γ₂ - α))
                →                         Γ₁ ⊢ V x α    →    Γ₂ ⊢ β
                                         --------------------------- ∃⁻
                →                             Γ₁ ∪ (Γ₂ - α) ⊢ β

\end{code}

Finally, we define the following shorthand.

\begin{code}

⊢_ : Formula → Set₁
⊢ α = ∅ ⊢ α


dm⊢ : ∀{Γ α} → Γ ⊢ α → Assembled formulaEq Γ
dm⊢ (cite x d) = dm⊢ d
dm⊢ (close x x₁ d) = x
dm⊢ (assume α) = from⟨ α ⟩
dm⊢ (arrowintro α d) = from dm⊢ d - α
dm⊢ (arrowelim d d₁) = from dm⊢ d ∪ dm⊢ d₁
dm⊢ (conjintro d d₁) = from dm⊢ d ∪ dm⊢ d₁
dm⊢ (conjelim d d₁) = from dm⊢ d ∪ (from from dm⊢ d₁ - _ - _)
dm⊢ (disjintro₁ β d) = dm⊢ d
dm⊢ (disjintro₂ α d) = dm⊢ d
dm⊢ (disjelim d d₁ d₂) = from dm⊢ d ∪ (from from dm⊢ d₁ - _ ∪ (from dm⊢ d₂ - _))
dm⊢ (univintro x x₁ d) = dm⊢ d
dm⊢ (univelim r x d) = dm⊢ d
dm⊢ (existintro r x x₁ d) = dm⊢ d
dm⊢ (existelim x₁ d d₁) = from dm⊢ d ∪ (from dm⊢ d₁ - _)


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
... | yes refl rewrite coident sub = d
... | no x≢y   = close
                  (dm⊢ d)
                  (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
                  (existelim (all⟨ V y (subNotFree (varterm x≢y) sub) ⟩
                              all∪ (α all~ (all- List.[ refl ])))
                   d
                   (existintro (varterm x) y (subInverse y∉α sub)
                    (assume α)))

\end{code}
