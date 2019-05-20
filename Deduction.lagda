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
Gentzen-style inferences.
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

\end{code}

It is trivial to show that the context of a deduction is assembled (and so
membership is decidable), simply by recursing over the deduction rules. The
proof is ommitted.
\begin{code}
assembled-context : ∀{Γ α} → Γ ⊢ α → Assembled formulaEq Γ
-- Proof omitted

\end{code}
\AgdaHide{
\begin{code}
assembled-context (cite _ d)           = assembled-context d
assembled-context (close AΓ _ d)       = AΓ
assembled-context (assume _)           = from⟨ _ ⟩
assembled-context (arrowintro _ d)     = from assembled-context d - _
assembled-context (arrowelim d₁ d₂)    = from assembled-context d₁ ∪ assembled-context d₂
assembled-context (conjintro d₁ d₂)    = from assembled-context d₁ ∪ assembled-context d₂
assembled-context (conjelim d₁ d₂)     = from assembled-context d₁ ∪ (from from assembled-context d₂ - _ - _)
assembled-context (disjintro₁ _ d)     = assembled-context d
assembled-context (disjintro₂ _ d)     = assembled-context d
assembled-context (disjelim d₁ d₂ d₃)  = from assembled-context d₁ ∪ (from from assembled-context d₂ - _ ∪ (from assembled-context d₃ - _))
assembled-context (univintro _ _ d)    = assembled-context d
assembled-context (univelim _ _ d)     = assembled-context d
assembled-context (existintro _ _ _ d) = assembled-context d
assembled-context (existelim _ d₁ d₂)  = from assembled-context d₁ ∪ (from assembled-context d₂ - _)

\end{code}
}


\begin{code}
rename      : ∀{Γ α α′}
              → α ≈ α′
              →                                Γ ⊢ α
                                              --------
              →                                Γ ⊢ α′
\end{code}
The atomic case is trivial, since an atomic formula is equivalent only to
itself.
\begin{code}
rename {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts) d = d
\end{code}
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\alpha \rightarrow \beta$}
      \AxiomC{[$\alpha'$]}
      \RightLabel{induction}
      \UnaryInfC{$\alpha$}
    \BinaryInfC{$\beta$}
    \RightLabel{induction}
    \UnaryInfC{$\beta'$}
    \RightLabel{$\rightarrow^-$}
    \UnaryInfC{$\alpha' \rightarrow \beta'$}
\end{prooftree}
\begin{code}
rename {Γ} {α ⇒ β} {α′ ⇒ β′} (apα ⇒ apβ) d =
  close
   (assembled-context d)
   (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂))
   (arrowintro α′
    (rename apβ
     (arrowelim
      d
      (rename (≈sym apα)
       (assume α′)))))
\end{code}
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\alpha \land \beta$}
    \AxiomC{[$\alpha$]}
    \RightLabel{induction}
    \UnaryInfC{$\alpha'$}
        \AxiomC{[$\beta$]}
        \RightLabel{induction}
        \UnaryInfC{$\beta'$}
      \RightLabel{$\land^+$}
      \BinaryInfC{$\alpha' \land \beta'$}
    \RightLabel{$\land^-$}
    \BinaryInfC{$\alpha' \land \beta'$}
\end{prooftree}
\begin{code}
rename {Γ} {α ∧ β} {α′ ∧ β′} (apα ∧ apβ) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ z₃))))
   (conjelim
    d
    (conjintro
     (rename apα
      (assume α))
     (rename apβ
      (assume β))))
\end{code}
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\alpha \lor \beta$}
    \AxiomC{[$\alpha$]}
    \RightLabel{induction}
    \UnaryInfC{$\alpha'$}
    \RightLabel{$\lor^+$}
    \UnaryInfC{$\alpha' \lor \beta'$}
      \AxiomC{[$\beta$]}
      \RightLabel{induction}
      \UnaryInfC{$\beta'$}
      \RightLabel{$\lor^+$}
      \UnaryInfC{$\alpha' \lor \beta'$}
    \RightLabel{$\lor^-$}
    \TrinaryInfC{$\alpha' \lor \beta'$}
\end{prooftree}
\begin{code}
rename {Γ} {α ∨ β} {α′ ∨ β′} (apα ∨ apβ) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
   (disjelim
    d
    (disjintro₁ β′
     (rename apα
      (assume α)))
    (disjintro₂ α′
     (rename apβ
      (assume β))))
\end{code}
We cannot assume that $x$ is not free in $\Gamma$.
\begin{prooftree}
  \AxiomC{[$\forall x \alpha$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\alpha$}
  \RightLabel{induction}
  \UnaryInfC{$\alpha'$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall x \alpha$}
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall x \alpha \rightarrow \forall x \alpha'$}
      \AxiomC{$\Gamma$}
      \UnaryInfC{$\vdots$}
      \UnaryInfC{$\forall x \alpha$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\forall x \alpha'$}
\end{prooftree}
\begin{code}
rename {Γ} {Λ x α} {Λ .x α′} (Λ y ap) d =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro x (all⟨ Λ∣ x α ⟩)
      (rename ap
       (univelim (varterm x) (ident α x)
        (assume (Λ x α))))))
    d)
\end{code}
Renaming $x$ to $y$ requires that $y$ is not free in $\alpha$, and so it is
also not free in $\forall x \alpha$.
\begin{prooftree}
  \AxiomC{[$\forall x \alpha$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\alpha[x/y]$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall y \alpha[x/y]$}
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall x \alpha \rightarrow \forall y \alpha[x/y]$}
      \AxiomC{$\Gamma$}
      \UnaryInfC{$\vdots$}
      \UnaryInfC{$\forall x \alpha$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\forall y \alpha[x/y]$}
\end{prooftree}
\begin{code}
rename {Γ} {Λ x α} {Λ y β} (Λ/ y∉α sub ap) d = ?
--  close
--   (assembled-context d)
--   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
--   (arrowelim
--    (arrowintro (Λ x α)
--     (univintro y (all⟨ Λ x y∉α ⟩)
--      (univelim (varterm y) sub
--       (assume (Λ x α)))))
--    d)
\end{code}
\begin{code}
rename {Γ} {Λ x α} {Λ y β} (Λ/′ ap y∉α sub) d = ?
--  close
--   (assembled-context d)
--   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
--   (arrowelim
--    (arrowintro (Λ x α)
--     (univintro y (all⟨ Λ x y∉α ⟩)
--      (univelim (varterm y) sub
--       (assume (Λ x α)))))
--    d)
\end{code}
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\exists x \alpha$}
      \AxiomC{[$\alpha$]}
      \RightLabel{induction}
      \UnaryInfC{$\alpha'$}
      \RightLabel{$\exists^+$}
      \UnaryInfC{$\exists x \alpha'$}
    \RightLabel{$\exists^-$}
    \BinaryInfC{$\exists x \alpha'$}
\end{prooftree}
\begin{code}
rename {Γ} {V x α} {V .x β} (V y ap) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) x (ident β x)
     (rename ap
      (assume α))))
\end{code}
This case is trivial if the variable is being replaced with itself. Note that
$x$ cannot be free in $\alpha[x/y]$, and so it is also not free in $\exists y
\alpha[x/y]$.
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\exists x \alpha$}
      \AxiomC{[$\alpha$]}
      \RightLabel{$\exists^+$}
      \UnaryInfC{$\exists y \alpha[x/y]$}
    \RightLabel{$\exists^-$}
    \BinaryInfC{$\exists y \alpha[x/y]$}
\end{prooftree}
\begin{code}
rename {Γ} {V x α} {V y β} (V/ y∉α sub ap) d = ? --with varEq x y
--... | yes refl rewrite subIdentFunc sub = d
--... | no x≢y   = close
--                  (assembled-context d)
--                  (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
--                  (existelim (all⟨ V y (subNotFree (varterm x≢y) sub) ⟩
--                              all∪ (all- all⟨- [ refl ] ⟩))
--                   d
--                   (existintro (varterm x) y (subInverse y∉α sub)
--                    (assume α)))
\end{code}
\begin{code}
rename {Γ} {V x α} {V y β} (V/′ ap y∉α sub) d = ? --with varEq x y
--... | yes refl rewrite subIdentFunc sub = d
--... | no x≢y   = close
--                  (assembled-context d)
--                  (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
--                  (existelim (all⟨ V y (subNotFree (varterm x≢y) sub) ⟩
--                              all∪ (all- all⟨- [ refl ] ⟩))
--                   d
--                   (existintro (varterm x) y (subInverse y∉α sub)
--                    (assume α)))

\end{code}
