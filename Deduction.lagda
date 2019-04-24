\begin{code}

module Deduction where

open import Agda.Builtin.String

open import Formula hiding (_∷_)
open import Menge
open import Decidable

private
  _NotFreeInAll_ : Variable → Pred Formula → Set
  x NotFreeInAll Γ = All (x NotFreeIn_) Γ

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

  close       : ∀{Γ Δ α} → Γ ⊂ Δ  → Γ ⊢ α → Δ ⊢ α

\end{code}
\todo{Justify}
\begin{code}

  univrename  : ∀{Γ α α[x/y] x y}
                → y NotFreeIn α → α [ x / varterm y ]≡ α[x/y]
                →                              Γ ⊢ Λ x α
                                            ----------------
                →                            Γ ⊢ Λ y α[x/y]

  existrename : ∀{Γ α α[x/y] x y}
                → y NotFreeIn α → α [ x / varterm y ]≡ α[x/y]
                →                              Γ ⊢ V x α
                                            ----------------
                →                            Γ ⊢ V y α[x/y]

\end{code}
The remaining constructors correspond to the usual natural deduction rules.
Agda's comment syntax (\inline{--}) allows these rules to be formatted as
Gentzen style inferences.
\begin{code}

  assume      : (α : Formula)
                →                              α ∷ ∅ ⊢ α

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
                → x NotFreeInAll (β ∷ (Γ₂ - α))
                →                         Γ₁ ⊢ V x α    →    Γ₂ ⊢ β
                                         --------------------------- ∃⁻
                →                             Γ₁ ∪ (Γ₂ - α) ⊢ β

\end{code}

Finally, we define the following shorthand.

\begin{code}

⊢_ : Formula → Set₁
⊢ α = ∅ ⊢ α

\end{code}
