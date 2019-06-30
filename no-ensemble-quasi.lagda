In a similar fashion to \citet{caiproplogicagda2015}, we could define a proof
system which is similar to natural deduction, which does not use list
computation in the main deduction rules. Instead, include a deduction rule for
weakening the context on the left, and allow assume to weaken the context on
the right. We show only the rules for implication and universal generalisation.

\AgdaHide{
\begin{code}

module no-ensemble-quasi where

open import Agda.Builtin.String

open import Formula
open import List
open import Decidable

private
  infix 300 _NotFreeInAll_
  _NotFreeInAll_ : Variable → List Formula → Set
  x NotFreeInAll Γ = All (x NotFreeIn_) Γ

\end{code}
}
\begin{code}

_++_ : List Formula → List Formula → List Formula
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infix 1 _⊢_ ⊢_
data _⊢_ : List Formula → Formula → Set where

\end{code}
\AgdaHide{
\begin{code}
  cite       : ∀{α} → String → [] ⊢ α → [] ⊢ α

\end{code}
}
\begin{code}
  assume     : ∀{Γ} → (α : Formula)
               →                              α ∷ Γ ⊢ α

  weaken     : ∀{Γ α} → (Δ : List Formula)
               →                                  Γ ⊢ α
                                              --------------
               →                               (Δ ++ Γ) ⊢ α

  arrowintro : ∀{Γ β} → (α : Formula)
               →                                α ∷ Γ ⊢ β
                                               ----------- ⇒⁺ α
               →                                Γ ⊢ α ⇒ β

\end{code}
\AgdaHide{
\begin{code}

  arrowelim  : ∀{Γ α β}
               →                       Γ ⊢ α ⇒ β    →    Γ ⊢ α
                                      ------------------------- ⇒⁻
               →                                 Γ ⊢ β

  conjintro  : ∀{Γ α β}
               →                          Γ ⊢ α    →    Γ ⊢ β
                                         --------------------- ∧⁺
               →                                Γ ⊢ α ∧ β

  conjelim   : ∀{Γ α β γ}
               →                      Γ ⊢ α ∧ β    →  α ∷ β ∷ Γ ⊢ γ
                                     -------------------------------- ∧⁻
               →                                 Γ ⊢ γ

  disjintro₁ : ∀{Γ α} → (β : Formula)
               →                                  Γ ⊢ α
                                               ----------- ∨⁺₁
               →                                Γ ⊢ α ∨ β

  disjintro₂ : ∀{Γ β} → (α : Formula)
               →                                  Γ ⊢ β
                                               ----------- ∨⁺₂
               →                                Γ ⊢ α ∨ β

  disjelim   : ∀{Γ α β γ}
               →              Γ ⊢ α ∨ β    →    α ∷ Γ ⊢ γ    →    β ∷ Γ ⊢ γ
                             ----------------------------------------------- ∨⁻
               →                                  Γ ⊢ γ

\end{code}
}
\begin{code}

  univintro  : ∀{Γ α} → (x : Variable)
               → x NotFreeInAll Γ
               →                                  Γ ⊢ α
                                               ----------- ∀⁺
               →                                Γ ⊢ Λ x α

  univelim   : ∀{Γ α x α[x/r]} → (r : Term)
               → α [ x / r ]≡ α[x/r]
               →                                Γ ⊢ Λ x α
                                               ------------ ∀⁻
               →                                Γ ⊢ α[x/r]

\end{code}
\AgdaHide{
\begin{code}

  existintro : ∀{Γ α α[x/r]} → (r : Term) → (x : Variable)
               → α [ x / r ]≡ α[x/r]
               →                                  Γ ⊢ α[x/r]
                                                 ------------ ∃⁺
               →                                  Γ ⊢ V x α

  existelim  : ∀{Γ α β x}
               → x NotFreeInAll (β ∷ Γ) -- does this work?
               →                      Γ ⊢ V x α    →    α ∷ Γ ⊢ β
                                     --------------------------- ∃⁻
               →                                 Γ ⊢ β


⊢_ : Formula → Set
⊢_ α = [] ⊢ α

\end{code}
}

This system does not describe natural deduction, since the context is not the
same as it is for natural deduction. Extra formulae are assumed. It also
requires weakening at each assumption. Weakening could be built into the
assumption definition, and can be solved by proof search, but it is not a usual
consideration when doing natural deduction by hand.

This system works for propositional logic. We again prove that $\alpha
\rightarrow \beta \rightarrow \gamma \vdash \beta \rightarrow \alpha
\rightarrow \gamma$.
\begin{code}

reorder : ∀ α β γ → α ⇒ β ⇒ γ ∷ [] ⊢ β ⇒ α ⇒ γ
reorder α β γ = arrowintro β
                 (arrowintro α
                  (arrowelim
                   (arrowelim
                    (weaken (α ∷ β ∷ [])
                     (assume (α ⇒ β ⇒ γ)))
                     (assume α))
                   (weaken (α ∷ [])
                    (assume β))))

\end{code}

The added assumptions become an issue for the first order case, due to the
restrictions on free variables. Consider the following proof.
\begin{prooftree}
\AxiomC{$\forall{x}Q{x} \rightarrow P{x}$}
  \AxiomC{$\forall{x}\left(\forall{x}A \rightarrow Q{x}\right)$}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\forall{x}A \rightarrow Q{x}$}
    \AxiomC{$\forall{x}A$}
  \RightLabel{$\rightarrow^-$}
  \BinaryInfC{$Q{x}$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall{x}Q{x}$}
\RightLabel{$\rightarrow^-$}
\BinaryInfC{$P{x}$}
\end{prooftree}
This is a valid natural deduction, and it was checked with the ensemble-based
natural deduction system. However, this proof tree does not satisfy the above
rules, since $\forall{x}A \rightarrow Q{x}$ would have to be made an extra
assumption above the deduction of $Qx$ by weakening. This means that the
universal generalisation introduction is not valid, since $x$ is free in an
open assumption.
