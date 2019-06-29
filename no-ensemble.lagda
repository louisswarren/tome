Lists could be used for the context of natural deduction trees, instead of using
ensembles. The operations for removal and union are still needed.
\AgdaHide{
\begin{code}

module no-ensemble where

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

infixl 5 _-_
_-_ : List Formula → Formula → List Formula
[] - β = []
(α ∷ αs) - β with formulaEq α β
((β ∷ αs) - .β) | yes refl = αs - β
((α ∷ αs) -  β) | no  _    = α ∷ (αs - β)

infixr 5 _∪_
_∪_ : List Formula → List Formula → List Formula
[]       ∪ ys = ys
(x ∷ xs) ∪ ys = x ∷ (xs ∪ ys)

\end{code}

\AgdaHide{
\begin{code}

infix 1 _⊢_ ⊢_
data _⊢_ : List Formula → Formula → Set where
  cite       : ∀{α} → String → [] ⊢ α → [] ⊢ α

  assume     : (α : Formula)
               →                              α ∷ [] ⊢ α

  arrowintro : ∀{Γ β} → (α : Formula)
               →                                  Γ ⊢ β
                                             --------------- ⇒⁺ α
               →                              Γ - α ⊢ α ⇒ β

  arrowelim  : ∀{Γ₁ Γ₂ α β}
               →                      Γ₁ ⊢ α ⇒ β    →    Γ₂ ⊢ α
                                     --------------------------- ⇒⁻
               →                            (Γ₁ ∪ Γ₂) ⊢ β

  conjintro  : ∀{Γ₁ Γ₂ α β}
               →                          Γ₁ ⊢ α    →    Γ₂ ⊢ β
                                         ----------------------- ∧⁺
               →                            (Γ₁ ∪ Γ₂) ⊢ α ∧ β

  conjelim   : ∀{Γ₁ Γ₂ α β γ}
               →                      Γ₁ ⊢ α ∧ β    →    Γ₂ ⊢ γ
                                     --------------------------- ∧⁻
               →                       Γ₁ ∪ ((Γ₂ - α) - β) ⊢ γ

  disjintro₁ : ∀{Γ α} → (β : Formula)
               →                                  Γ ⊢ α
                                               ----------- ∨⁺₁
               →                                Γ ⊢ α ∨ β

  disjintro₂ : ∀{Γ β} → (α : Formula)
               →                                  Γ ⊢ β
                                               ----------- ∨⁺₂
               →                                Γ ⊢ α ∨ β

  disjelim   : ∀{Γ₁ Γ₂ Γ₃ α β γ}
               →              Γ₁ ⊢ α ∨ β    →    Γ₂ ⊢ γ    →    Γ₃ ⊢ γ
                             ------------------------------------------ ∨⁻
               →                   (Γ₁ ∪ (Γ₂ - α)) ∪ (Γ₃ - β) ⊢ γ

  univintro  : ∀{Γ α} → (x : Variable)
               → x NotFreeInAll Γ
               →                                  Γ ⊢ α
                                               ----------- ∀⁺
               →                                Γ ⊢ Λ x α

  univelim   : ∀{Γ α x α[x/r]} → (r : Term)
               → α [ x / r ]≡ α[x/r]
               →                                  Γ ⊢ Λ x α
                                                 ------------ ∀⁻
               →                                  Γ ⊢ α[x/r]

  existintro : ∀{Γ α α[x/r]} → (r : Term) → (x : Variable)
               → α [ x / r ]≡ α[x/r]
               →                                  Γ ⊢ α[x/r]
                                                 ------------ ∃⁺
               →                                  Γ ⊢ V x α

  existelim  : ∀{Γ₁ Γ₂ α β x}
               → x NotFreeInAll (β ∷ (Γ₂ - α))
               →                      Γ₁ ⊢ V x α    →    Γ₂ ⊢ β
                                     --------------------------- ∃⁻
               →                          Γ₁ ∪ (Γ₂ - α) ⊢ β


⊢_ : Formula → Set
⊢_ α = [] ⊢ α

\end{code}
}

However, it is now more complicated to prove that a given deduction's context
is a subset of the permitted open assumptions. It is now necessary to reason
about the result of a computation. Begin with the following trivial lemma.

\begin{code}

eqcontext : ∀{α Δ Γ}→ Δ ≡ Γ → Δ ⊢ α → Γ ⊢ α
eqcontext refl x = x

\end{code}

The proof for $\vdash \alpha \rightarrow \alpha$ is as follows
\begin{code}

arrow-example : ∀ α → ⊢ α ⇒ α
arrow-example α = eqcontext closed
                   (arrowintro α
                    (assume α))
                  where
                    closed : ((α ∷ []) - α) ≡ []
                    closed with formulaEq α α
                    ...    | yes refl = refl
                    ...    | no  α≢α  = ⊥-elim (α≢α refl)

\end{code}
To examine what the result of \inline{(α ∷ []) - α} is, we must examine the
pattern matching that occurs on the result of \inline{formulaEq α α}. In the
real case where \inline{α ≡ α} holds, $\alpha$ is removed from the list, and
the proof is \inline{refl}. However, we must also consider the case where
\inline{α ≢ α} (which we prove using absurdity).

\AgdaHide{
\begin{code}

removeonce : ∀ α → ((α ∷ α ∷ []) - α) ≡ []
removeonce α with formulaEq α α
removeonce α | yes refl with formulaEq α α
removeonce α | yes refl | yes refl = refl
removeonce α | yes refl | no x = ⊥-elim (x refl)
removeonce α | no x = ⊥-elim (x refl)

simple₂ : ∀ α β → [] ⊢ α ⇒ α ∧ (β ⇒ α)
simple₂ α β = eqcontext closed (arrowintro α (conjintro (assume α) (arrowintro β (assume α))))
  where
    closed : (((α ∷ []) ∪ ((α ∷ []) - β)) - α) ≡ []
    closed with formulaEq α β
    closed | yes refl with formulaEq α α
    closed | yes refl | yes refl = refl
    closed | yes refl | no x = ⊥-elim (x refl)
    closed | no _ with formulaEq α α
    closed | no _ | yes refl with formulaEq α α
    closed | no _ | yes refl | yes refl = refl
    closed | no _ | yes refl | no x = ⊥-elim (x refl)
    closed | no _ | no x = ⊥-elim (x refl)

\end{code}
}

Now, consider a more complicated example; we prove that $\alpha \rightarrow
\beta \rightarrow \gamma \vdash \beta \rightarrow \alpha \rightarrow \gamma$.
\begin{code}

reorder : ∀ α β γ → α ⇒ β ⇒ γ ∷ [] ⊢ β ⇒ α ⇒ γ
reorder α β γ = eqcontext closed
                (arrowintro β
                 (arrowintro α
                  (arrowelim
                   (arrowelim
                    (assume (α ⇒ β ⇒ γ))
                    (assume α))
                   (assume β))))
  where
    closed : ((α ⇒ β ⇒ γ ∷ α ∷ β ∷ []) - α - β) ≡ α ⇒ β ⇒ γ ∷ []
    closed with formulaEq (α ⇒ β ⇒ γ) α
    closed | yes ()
    closed | no _ with formulaEq α α
    closed | no _ | no  α≢α  = ⊥-elim (α≢α refl)
    closed | no _ | yes refl with formulaEq β α
    closed | no _ | yes refl | yes refl with formulaEq (α ⇒ β ⇒ γ) β
    closed | no _ | yes refl | yes refl | yes ()
    closed | no _ | yes refl | yes refl | no _ = refl
    closed | no _ | yes refl | no _ with formulaEq (α ⇒ β ⇒ γ) β
    closed | no _ | yes refl | no _ | yes ()
    closed | no _ | yes refl | no _ | no _ with formulaEq β β
    closed | no _ | yes refl | no _ | no _ | yes refl = refl
    closed | no _ | yes refl | no _ | no _ | no  β≢β  = ⊥-elim (β≢β refl)

\end{code}
Each equality check must be examined. Clearly this becomes unwieldy, even in
simple cases. Moreover, Agda's proof search will not create \inline{with}
blocks, and so is of little use here.
