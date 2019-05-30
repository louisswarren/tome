\begin{code}

open import Decidable
open import Deduction
open import Ensemble
open import Formula
open import List
open import Vec

\end{code}

\subsection{Formula equivalence}

Formulae are equivalent if they are equal up to renaming bound variables. Here,
renaming means substituting a variable for another variable which is not free,
so that the meaning of the formula does not change.
\begin{code}

infix 50 _≈_
data _≈_ : Formula → Formula → Set where
  atom : ∀ r ts → atom r ts ≈ atom r ts
  _⇒_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ⇒ β ≈ α′ ⇒ β′
  _∧_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ∧ β ≈ α′ ∧ β′
  _∨_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ∨ β ≈ α′ ∨ β′
  Λ    : ∀{α α′} → ∀ x → α ≈ α′ → Λ x α ≈ Λ x α′
  V    : ∀{α α′} → ∀ x → α ≈ α′ → V x α ≈ V x α′
  Λ/   : ∀{α β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β
                       → β ≈ β′ → Λ x α ≈ Λ y β′
  V/   : ∀{α β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β
                       → β ≈ β′ → V x α ≈ V y β′
  Λ/′  : ∀{α α′ β′ x y} → α ≈ α′ → y NotFreeIn α′
                        → α′ [ x / varterm y ]≡ β′ → Λ x α ≈ Λ y β′
  V/′  : ∀{α α′ β′ x y} → α ≈ α′ → y NotFreeIn α′
                        → α′ [ x / varterm y ]≡ β′ → V x α ≈ V y β′

\end{code}

It is important that this relation is symmetric
\begin{code}

≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α
≈sym (atom r ts) = atom r ts
≈sym (α≈α′ ⇒ β≈β′) = ≈sym α≈α′ ⇒ ≈sym β≈β′
≈sym (α≈α′ ∧ β≈β′) = ≈sym α≈α′ ∧ ≈sym β≈β′
≈sym (α≈α′ ∨ β≈β′) = ≈sym α≈α′ ∨ ≈sym β≈β′
≈sym (Λ x α≈α′) = Λ x (≈sym α≈α′)
≈sym (V x α≈α′) = V x (≈sym α≈α′)
≈sym {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = Λ x (≈sym β≈β′)
...    | no x≢y = Λ/′ (≈sym β≈β′) (subNotFree (varterm x≢y) α[x/y]≡β) (subInverse y∉α α[x/y]≡β)
≈sym {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = V x (≈sym β≈β′)
...    | no x≢y = V/′ (≈sym β≈β′) (subNotFree (varterm x≢y) α[x/y]≡β) (subInverse y∉α α[x/y]≡β)
≈sym {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′) with varEq x y
...    | yes refl rewrite subIdentFunc α′[x/y]≡β′ = Λ x (≈sym α≈α′)
...    | no  x≢y  = Λ/ (subNotFree (varterm x≢y) α′[x/y]≡β′) (subInverse y∉α′ α′[x/y]≡β′) (≈sym α≈α′)
≈sym {V x α} {V y β′} (V/′ α≈α′ y∉α′ α′[x/y]≡β′) with varEq x y
...    | yes refl rewrite subIdentFunc α′[x/y]≡β′ = V x (≈sym α≈α′)
...    | no  x≢y  = V/ (subNotFree (varterm x≢y) α′[x/y]≡β′) (subInverse y∉α′ α′[x/y]≡β′) (≈sym α≈α′)

\end{code}

\begin{code}

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


\end{code}
\begin{code}
-- should allow different levels
record _↔_ {a} (A : Set a) (B : Set a) : Set a where
  field
    ⟨→⟩ : A → B
    ⟨←⟩ : B → A
open _↔_


renameIff : ∀{Γ α α′} → α ≈ α′ → (Γ ⊢ α) ↔ (Γ ⊢ α′)
\end{code}
The atomic case is trivial, since an atomic formula is equivalent only to
itself.
\begin{code}
⟨→⟩ (renameIff {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts)) d = d
⟨←⟩ (renameIff {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts)) d = d
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
⟨→⟩ (renameIff {Γ} {α ⇒ β} {α′ ⇒ β′} (apα ⇒ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂))
   (arrowintro α′
    (⟨→⟩ (renameIff apβ)
     (arrowelim
      d
      (⟨←⟩ (renameIff apα) -- Would not be structurally recursive
       (assume α′)))))
⟨←⟩ (renameIff {Γ} {α ⇒ β} {α′ ⇒ β′} (apα ⇒ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂))
   (arrowintro α
    (⟨←⟩ (renameIff apβ)
     (arrowelim
      d
      (⟨→⟩ (renameIff apα) -- Would not be structurally recursive
       (assume α)))))
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
⟨→⟩ (renameIff {Γ} {α ∧ β} {α′ ∧ β′} (apα ∧ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ z₃))))
   (conjelim
    d
    (conjintro
     (⟨→⟩ (renameIff apα)
      (assume α))
     (⟨→⟩ (renameIff apβ)
      (assume β))))
⟨←⟩ (renameIff {Γ} {α ∧ β} {α′ ∧ β′} (apα ∧ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ z₃))))
   (conjelim
    d
    (conjintro
     (⟨←⟩ (renameIff apα)
      (assume α′))
     (⟨←⟩ (renameIff apβ)
      (assume β′))))
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
⟨→⟩ (renameIff {Γ} {α ∨ β} {α′ ∨ β′} (apα ∨ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
   (disjelim
    d
    (disjintro₁ β′
     (⟨→⟩ (renameIff apα)
      (assume α)))
    (disjintro₂ α′
     (⟨→⟩ (renameIff apβ)
      (assume β))))
⟨←⟩ (renameIff {Γ} {α ∨ β} {α′ ∨ β′} (apα ∨ apβ)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
   (disjelim
    d
    (disjintro₁ β
     (⟨←⟩ (renameIff apα)
      (assume α′)))
    (disjintro₂ α
     (⟨←⟩ (renameIff apβ)
      (assume β′))))
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
⟨→⟩ (renameIff {Γ} {Λ x α} {Λ .x α′} (Λ y ap)) d =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro x (all⟨ Λ∣ x α ⟩)
      (⟨→⟩ (renameIff ap)
       (univelim (varterm x) (ident α x)
        (assume (Λ x α))))))
    d)
⟨←⟩ (renameIff {Γ} {Λ x α} {Λ .x α′} (Λ y ap)) d =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α′)
     (univintro x (all⟨ Λ∣ x α′ ⟩)
      (⟨←⟩ (renameIff ap)
       (univelim (varterm x) (ident α′ x)
        (assume (Λ x α′))))))
    d)
\end{code}
Renaming $x$ to $y$ requires that $y$ is not free in $\alpha$, and so it is
also not free in $\forall x \alpha$. \todo{Update}
%\begin{prooftree}
%  \AxiomC{[$\forall x \alpha$]}
%  \RightLabel{$\forall^-$}
%  \UnaryInfC{$\alpha[x/y]$}
%  \RightLabel{$\forall^+$}
%  \UnaryInfC{$\forall y \alpha[x/y]$}
%  \RightLabel{$\rightarrow^+$}
%  \UnaryInfC{$\forall x \alpha \rightarrow \forall y \alpha[x/y]$}
%      \AxiomC{$\Gamma$}
%      \UnaryInfC{$\vdots$}
%      \UnaryInfC{$\forall x \alpha$}
%    \RightLabel{$\rightarrow^-$}
%    \BinaryInfC{$\forall y \alpha[x/y]$}
%\end{prooftree}
\begin{code}
⟨→⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′)) d =
  close
    (assembled-context d)
    (λ x₁ z → z (λ z₁ → z₁ (λ z₂ → z₂)))
    (arrowelim
     (arrowintro (Λ x α)
      (univintro y all⟨ Λ x y∉α ⟩
       (⟨→⟩ (renameIff β≈β′)
        (univelim (varterm y) α[x/y]≡β
         (assume (Λ x α))))))
     d)
⟨←⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′)) d with varEq x y
... | yes refl rewrite subIdentFunc α[x/y]≡β =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x β′)
     (univintro x all⟨ Λ∣ x β′ ⟩
      (⟨←⟩ (renameIff β≈β′)
       (univelim (varterm x) (ident β′ x)
        (assume (Λ x β′))))))
    d)
... | no  x≢y  =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ y β′)
     (univintro x all⟨ Λ y (≈notfree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β)) ⟩
      (univelim (varterm x) (subInverse y∉α α[x/y]≡β)
       (univintro y all⟨ Λ∣ y β′ ⟩
        (⟨←⟩ (renameIff β≈β′)
         (univelim (varterm y) (ident β′ y)
          (assume (Λ y β′))))))))
    d)
\end{code}
\begin{code}
⟨→⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′)) d =
  close
   (assembled-context d)
   (λ x₁ z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro y all⟨ ≈notfree (Λ x (≈sym α≈α′)) (Λ x y∉α′) ⟩
      (univelim (varterm y) α′[x/y]≡β′
       (univintro x all⟨ Λ∣ x α ⟩
        (⟨→⟩ (renameIff α≈α′) -- Not structurally recursive
         (univelim (varterm x) (ident α x)
          (assume (Λ x α))))))))
    d)
⟨←⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′)) d with varEq x y
... | yes refl rewrite subIdentFunc α′[x/y]≡β′ =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x β′)
     (univintro x all⟨ Λ∣ x β′ ⟩ -- Only difference
      (⟨←⟩ (renameIff α≈α′)
       (univelim (varterm x) (ident β′ x)
        (assume (Λ x β′))))))
    d)
... | no  x≢y  =
  close
   (assembled-context d)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ y β′)
     (univintro x all⟨ Λ y (subNotFree (varterm x≢y) α′[x/y]≡β′) ⟩ -- Only difference
      (⟨←⟩ (renameIff α≈α′)
       (univelim (varterm x) (subInverse y∉α′ α′[x/y]≡β′)
        (assume (Λ y β′))))))
    d)
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
⟨→⟩ (renameIff {Γ} {V x α} {V .x β} (V y ap)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) x (ident β x)
     (⟨→⟩ (renameIff ap)
      (assume α))))
⟨←⟩ (renameIff {Γ} {V x α} {V .x β} (V y ap)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm x) x (ident α x)
     (⟨←⟩ (renameIff ap)
      (assume β))))
\end{code}
This case is trivial if the variable is being replaced with itself. Note that
$x$ cannot be free in $\alpha[x/y]$, and so it is also not free in $\exists y
\alpha[x/y]$. \todo{Update}
%\begin{prooftree}
%  \AxiomC{$\Gamma$}
%  \UnaryInfC{$\vdots$}
%  \UnaryInfC{$\exists x \alpha$}
%      \AxiomC{[$\alpha$]}
%      \RightLabel{$\exists^+$}
%      \UnaryInfC{$\exists y \alpha[x/y]$}
%    \RightLabel{$\exists^-$}
%    \BinaryInfC{$\exists y \alpha[x/y]$}
%\end{prooftree}
\begin{code}
⟨→⟩ (renameIff {Γ} {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′)) d with varEq x y
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
      (⟨→⟩ (renameIff β≈β′) -- Not structurally recursive
       (assume _)))))
... | yes refl with subIdentFunc α[x/y]≡β
...            | refl =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β′ ⟩ all∪ (all- all⟨ y∉α ⟩))
    d
    (existintro (varterm x) x (ident β′ x)
     (⟨→⟩ (renameIff β≈β′)
      (assume α))))
⟨←⟩ (renameIff {Γ} {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′)) d =
  close
   (assembled-context d)
   (λ x₁ x₂ x₃ → x₂ x₃ λ x₄ → x₄ λ x₅ → x₅)
   (existelim (all⟨ V x y∉α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    d
    (existintro (varterm y) x α[x/y]≡β
     (⟨←⟩ (renameIff β≈β′)
      (assume β′))))
\end{code}
\begin{code}
⟨→⟩ (renameIff {Γ} {V x α} {V y β} (V/′ α≈α′ y∉α′ α′[x/y]≡β′)) d with varEq x y
... | yes refl rewrite subIdentFunc α′[x/y]≡β′ =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β ⟩ all∪ (all- all⟨- [ refl ] ⟩)) -- Differs here
    d
    (existintro (varterm x) x (ident β x) -- And here
     (⟨→⟩ (renameIff α≈α′) -- Not structurally recursive
      (assume α))))
... | no x≢y   =
  close
   (assembled-context d)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V y (subNotFree (varterm x≢y) α′[x/y]≡β′) ⟩
               all∪ (all- all⟨- [ refl ] ⟩)) -- Differs here
    d
    (existintro (varterm x) y (subInverse y∉α′ α′[x/y]≡β′) -- And here
     (⟨→⟩ (renameIff α≈α′)
      (assume α))))
⟨←⟩ (renameIff {Γ} {V x α} {V y β′} (V/′ α≈α′ y∉α′ α′[x/y]≡β′)) d =
  close
   (assembled-context d)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ z₃ (λ z₅ → z₅ (λ z₆ → z₆)))))
   (existelim (all⟨ V x (≈notfree (≈sym α≈α′) y∉α′) ⟩
               all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- all⟨ y∉α′ ⟩))))
    d
    (existelim (all⟨ V∣ x α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
     (existintro (varterm y) x α′[x/y]≡β′
      (assume β′))
     (existintro (varterm x) x (ident α x)
      (⟨←⟩ (renameIff α≈α′)
       (assume _)))))

rename      : ∀{Γ α α′}
              → α ≈ α′
              →                                Γ ⊢ α
                                              --------
              →                                Γ ⊢ α′
rename α≈α′ = ⟨→⟩ (renameIff α≈α′)
\end{code}
