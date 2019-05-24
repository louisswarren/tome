--STRIP: \begin{code}

--STRIP: module Deduction where

open import Agda.Builtin.String
open import Agda.Builtin.Nat renaming (Nat to ℕ) using (suc ; _+_)

open import Decidable
open import Ensemble
open import Formula-stripped
open import List

private
  _NotFreeInAll_ : Variable → Pred Formula → Set₁
  x NotFreeInAll Γ = Ensemble.All (x NotFreeIn_) Γ

infix 1 _⊢_ ⊢_
data _⊢_ : Pred Formula → Formula → Set₁ where

--STRIP: \end{code}
--STRIP: The first constructor is used for typesetting later; a deduction can be
--STRIP: abbreviated to a label. This will be used for lemmas, and for applying assumed
--STRIP: axiom schemes.
--STRIP: \begin{code}

  cite        : ∀{α} → String → ∅ ⊢ α → ∅ ⊢ α

--STRIP: \end{code}
--STRIP: The following constructor exists for two reasons:
--STRIP: \begin{enumerate}
--STRIP:   \item If $\Gamma \vdash \alpha$ then $\Gamma, \beta \vdash \alpha$
--STRIP:   \item We want to be able to normalise $\Gamma$, for example from $\{\alpha\}
--STRIP:     \setminus \alpha$ to $\emptyset$.
--STRIP: \end{enumerate}
--STRIP: \begin{code}

  close       : ∀{Γ Δ α} → Assembled formulaEq Δ → Γ ⊂ Δ → Γ ⊢ α → Δ ⊢ α

--STRIP: \end{code}
--STRIP: The remaining constructors correspond to the usual natural deduction rules.
--STRIP: Agda's comment syntax (\inline{--}) allows these rules to be formatted as
--STRIP: Gentzen-style inferences.
--STRIP: \begin{code}

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

--STRIP: \end{code}
--STRIP: The constructors for first order logic require an extra proof to be supplied,
--STRIP: either of variable boundedness or variable replacement. The propositions proved
--STRIP: here have been formulated so that Agda's built-in proof search should be able to
--STRIP: supply them.
--STRIP: \begin{code}

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

--STRIP: \end{code}
--STRIP: 
--STRIP: Finally, we define the following shorthand.
--STRIP: \begin{code}

⊢_ : Formula → Set₁
⊢ α = ∅ ⊢ α

--STRIP: \end{code}
--STRIP: 
--STRIP: It is trivial to show that the context of a deduction is assembled (and so
--STRIP: membership is decidable), simply by recursing over the deduction rules. The
--STRIP: proof is ommitted.
--STRIP: \begin{code}
assembled-context : ∀{Γ α} → Γ ⊢ α → Assembled formulaEq Γ
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}
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

--STRIP: \end{code}
--STRIP: }
--STRIP: 
--STRIP: \begin{code}
rename      : ∀{Γ α α′ n}
              → ∣ α ∣≡ n
              → α ≈ α′
              →                                Γ ⊢ α
                                              --------
              →                                Γ ⊢ α′
--STRIP: \end{code}
--STRIP: The atomic case is trivial, since an atomic formula is equivalent only to
--STRIP: itself.
--STRIP: \begin{code}
rename {Γ} {atom r ts} {.(atom r ts)} sz (atom .r .ts) d = d
--STRIP: \end{code}
--STRIP: \begin{prooftree}
--STRIP:   \AxiomC{$\Gamma$}
--STRIP:   \UnaryInfC{$\vdots$}
--STRIP:   \UnaryInfC{$\alpha \rightarrow \beta$}
--STRIP:       \AxiomC{[$\alpha'$]}
--STRIP:       \RightLabel{induction}
--STRIP:       \UnaryInfC{$\alpha$}
--STRIP:     \BinaryInfC{$\beta$}
--STRIP:     \RightLabel{induction}
--STRIP:     \UnaryInfC{$\beta'$}
--STRIP:     \RightLabel{$\rightarrow^-$}
--STRIP:     \UnaryInfC{$\alpha' \rightarrow \beta'$}
--STRIP: \end{prooftree}
--STRIP: \begin{code}
rename {Γ} {α ⇒ β} {α′ ⇒ β′} ((n ⇒ m) szα szβ) (apα ⇒ apβ) d =
  close
   (assembled-context d)
   (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂))
   (arrowintro α′
    (rename szβ apβ
     (arrowelim
      d
      (rename (≈size (≈sym apα) szα) (≈sym apα) -- Not structurally recursive
       (assume α′)))))
--STRIP: \end{code}
--STRIP: \begin{prooftree}
--STRIP:   \AxiomC{$\Gamma$}
--STRIP:   \UnaryInfC{$\vdots$}
--STRIP:   \UnaryInfC{$\alpha \land \beta$}
--STRIP:     \AxiomC{[$\alpha$]}
--STRIP:     \RightLabel{induction}
--STRIP:     \UnaryInfC{$\alpha'$}
--STRIP:         \AxiomC{[$\beta$]}
--STRIP:         \RightLabel{induction}
--STRIP:         \UnaryInfC{$\beta'$}
--STRIP:       \RightLabel{$\land^+$}
--STRIP:       \BinaryInfC{$\alpha' \land \beta'$}
--STRIP:     \RightLabel{$\land^-$}
--STRIP:     \BinaryInfC{$\alpha' \land \beta'$}
--STRIP: \end{prooftree}
--STRIP: \begin{code}
rename {Γ} {α ∧ β} {α′ ∧ β′} ((n ∧ m) szα szβ) (apα ∧ apβ) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ z₃))))
   (conjelim
    d
    (conjintro
     (rename szα apα
      (assume α))
     (rename szβ apβ
      (assume β))))
--STRIP: \end{code}
--STRIP: \begin{prooftree}
--STRIP:   \AxiomC{$\Gamma$}
--STRIP:   \UnaryInfC{$\vdots$}
--STRIP:   \UnaryInfC{$\alpha \lor \beta$}
--STRIP:     \AxiomC{[$\alpha$]}
--STRIP:     \RightLabel{induction}
--STRIP:     \UnaryInfC{$\alpha'$}
--STRIP:     \RightLabel{$\lor^+$}
--STRIP:     \UnaryInfC{$\alpha' \lor \beta'$}
--STRIP:       \AxiomC{[$\beta$]}
--STRIP:       \RightLabel{induction}
--STRIP:       \UnaryInfC{$\beta'$}
--STRIP:       \RightLabel{$\lor^+$}
--STRIP:       \UnaryInfC{$\alpha' \lor \beta'$}
--STRIP:     \RightLabel{$\lor^-$}
--STRIP:     \TrinaryInfC{$\alpha' \lor \beta'$}
--STRIP: \end{prooftree}
--STRIP: \begin{code}
rename {Γ} {α ∨ β} {α′ ∨ β′} ((n ∨ m) szα szβ) (apα ∨ apβ) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
   (disjelim
    d
    (disjintro₁ β′
     (rename szα apα
      (assume α)))
    (disjintro₂ α′
     (rename szβ apβ
      (assume β))))
--STRIP: \end{code}
--STRIP: We cannot assume that $x$ is not free in $\Gamma$.
--STRIP: \begin{prooftree}
--STRIP:   \AxiomC{[$\forall x \alpha$]}
--STRIP:   \RightLabel{$\forall^-$}
--STRIP:   \UnaryInfC{$\alpha$}
--STRIP:   \RightLabel{induction}
--STRIP:   \UnaryInfC{$\alpha'$}
--STRIP:   \RightLabel{$\forall^+$}
--STRIP:   \UnaryInfC{$\forall x \alpha$}
--STRIP:   \RightLabel{$\rightarrow^+$}
--STRIP:   \UnaryInfC{$\forall x \alpha \rightarrow \forall x \alpha'$}
--STRIP:       \AxiomC{$\Gamma$}
--STRIP:       \UnaryInfC{$\vdots$}
--STRIP:       \UnaryInfC{$\forall x \alpha$}
--STRIP:     \RightLabel{$\rightarrow^-$}
--STRIP:     \BinaryInfC{$\forall x \alpha'$}
--STRIP: \end{prooftree}
--STRIP: \begin{code}
rename {Γ} {Λ x α} {Λ .x α′} (Λ n sz) (Λ y ap) d =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro x (all⟨ Λ∣ x α ⟩)
      (rename sz ap
       (univelim (varterm x) (ident α x)
        (assume (Λ x α))))))
    d)
--STRIP: \end{code}
--STRIP: Renaming $x$ to $y$ requires that $y$ is not free in $\alpha$, and so it is
--STRIP: also not free in $\forall x \alpha$. \todo{Update}
--STRIP: %\begin{prooftree}
--STRIP: %  \AxiomC{[$\forall x \alpha$]}
--STRIP: %  \RightLabel{$\forall^-$}
--STRIP: %  \UnaryInfC{$\alpha[x/y]$}
--STRIP: %  \RightLabel{$\forall^+$}
--STRIP: %  \UnaryInfC{$\forall y \alpha[x/y]$}
--STRIP: %  \RightLabel{$\rightarrow^+$}
--STRIP: %  \UnaryInfC{$\forall x \alpha \rightarrow \forall y \alpha[x/y]$}
--STRIP: %      \AxiomC{$\Gamma$}
--STRIP: %      \UnaryInfC{$\vdots$}
--STRIP: %      \UnaryInfC{$\forall x \alpha$}
--STRIP: %    \RightLabel{$\rightarrow^-$}
--STRIP: %    \BinaryInfC{$\forall y \alpha[x/y]$}
--STRIP: %\end{prooftree}
--STRIP: \begin{code}
rename {Γ} {Λ x α} {Λ y β′} (Λ n sz) (Λ/ y∉α α[x/y]≡β β≈β′) d =
  close
    (assembled-context d)
    (λ x₁ z → z (λ z₁ → z₁ (λ z₂ → z₂)))
    (arrowelim
     (arrowintro (Λ x α)
      (univintro y all⟨ Λ x y∉α ⟩
       (rename (subSize α[x/y]≡β sz) β≈β′
        (univelim (varterm y) α[x/y]≡β
         (assume (Λ x α))))))
     d)
--STRIP: \end{code}
--STRIP: \begin{code}
rename {Γ} {Λ x α} {Λ y β′} {suc .n} (Λ n sz) (Λ/′ α≈α′ y∉α′ α′[x/y]≡β) d =
  close
    (assembled-context d)
    (λ x₁ z → z (λ z₁ → z₁ (λ z₂ → z₂)))
    (arrowelim
     (arrowintro (Λ x α)
      (univintro y all⟨ ≈notfree (Λ x (≈sym α≈α′)) (Λ x y∉α′) ⟩
       (univelim (varterm y) α′[x/y]≡β
        (univintro x all⟨ Λ∣ x α ⟩
         (rename {n = n} sz α≈α′ -- Not structurally recursive
          (univelim (varterm x) (ident α x)
           (assume (Λ x α))))))))
     d)
--STRIP: \end{code}
--STRIP: \begin{prooftree}
--STRIP:   \AxiomC{$\Gamma$}
--STRIP:   \UnaryInfC{$\vdots$}
--STRIP:   \UnaryInfC{$\exists x \alpha$}
--STRIP:       \AxiomC{[$\alpha$]}
--STRIP:       \RightLabel{induction}
--STRIP:       \UnaryInfC{$\alpha'$}
--STRIP:       \RightLabel{$\exists^+$}
--STRIP:       \UnaryInfC{$\exists x \alpha'$}
--STRIP:     \RightLabel{$\exists^-$}
--STRIP:     \BinaryInfC{$\exists x \alpha'$}
--STRIP: \end{prooftree}
--STRIP: \begin{code}
rename {Γ} {V x α} {V .x β} (V n sz) (V y ap) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) x (ident β x)
     (rename sz ap
      (assume α))))
--STRIP: \end{code}
--STRIP: This case is trivial if the variable is being replaced with itself. Note that
--STRIP: $x$ cannot be free in $\alpha[x/y]$, and so it is also not free in $\exists y
--STRIP: \alpha[x/y]$. \todo{Update}
--STRIP: %\begin{prooftree}
--STRIP: %  \AxiomC{$\Gamma$}
--STRIP: %  \UnaryInfC{$\vdots$}
--STRIP: %  \UnaryInfC{$\exists x \alpha$}
--STRIP: %      \AxiomC{[$\alpha$]}
--STRIP: %      \RightLabel{$\exists^+$}
--STRIP: %      \UnaryInfC{$\exists y \alpha[x/y]$}
--STRIP: %    \RightLabel{$\exists^-$}
--STRIP: %    \BinaryInfC{$\exists y \alpha[x/y]$}
--STRIP: %\end{prooftree}
--STRIP: \begin{code}
rename {Γ} {V x α} {V y β′} (V n sz) (V/ y∉α α[x/y]≡β β≈β′) d with varEq x y
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
      (rename (subSize α[x/y]≡β sz) β≈β′ -- Not structurally recursive
       (assume _)))))
... | yes refl with subIdentFunc α[x/y]≡β
...            | refl =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β′ ⟩ all∪ (all- all⟨ y∉α ⟩))
    d
    (existintro (varterm x) x (ident β′ x)
     (rename sz β≈β′
      (assume α))))
--STRIP: \end{code}
--STRIP: \begin{code}
rename {Γ} {V x α} {V y β} (V n sz) (V/′ α≈α′ y∉α′ α′[x/y]≡β) d with varEq x y
... | yes refl rewrite subIdentFunc α′[x/y]≡β =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) x (ident β x)
     (rename sz α≈α′ -- Not structurally recursive
      (assume α))))
... | no x≢y   =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V y (subNotFree (varterm x≢y) α′[x/y]≡β) ⟩
               all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) y (subInverse y∉α′ α′[x/y]≡β)
     (rename sz α≈α′
      (assume α))))

--STRIP: \end{code}
