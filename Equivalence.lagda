Usual \todo{specify?} treatments of formulae assume equivalence of formulae up
to renaming of bound variables. This has not been included in the definition of
formulae or of natural deduction. To do so would introduce an extra
complication to the deduction rules, as every step in a natural deduction proof
would have to include a proof that the conclusion is equivalent to the desired
one. However, it is possible to prove that this is unnecessary; given the sytem
above, if $\Gamma \vdash \alpha$ and $\alpha$ is equivalent to $\alpha'$ up to
the renaming of bound variables, then $\Gamma \vdash \alpha'$.
\begin{code}

module Equivalence where

open import Agda.Primitive using (_⊔_)

open import Decidable
open import Deduction
open import Ensemble
open import Formula
open import List
open import Vec

\end{code}

\subsection{Formula equivalence}

Formulae are \emph{equivalent} if they are equal up to renaming bound
variables. Here, renaming means substituting a variable for another variable
which is not free, so that the meaning of the formula does not change.
\begin{code}

infix 50 _≈_
data _≈_ : Formula → Formula → Set where
\end{code}
First, the trivial cases for equivalence, coming from equivalence of components.
\begin{code}
  atom : ∀ r ts → atom r ts ≈ atom r ts
  _⇒_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ⇒ β ≈ α′ ⇒ β′
  _∧_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ∧ β ≈ α′ ∧ β′
  _∨_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ∨ β ≈ α′ ∨ β′
  Λ    : ∀{α α′} → ∀ x → α ≈ α′ → Λ x α ≈ Λ x α′
  V    : ∀{α α′} → ∀ x → α ≈ α′ → V x α ≈ V x α′
\end{code}
Now, the case for renaming the quantifying variable of a generalisation. The
resulting component must also be replaceable with an equivalent component, as
other bound variable renaming may occur inside.
\begin{code}
  Λ/   : ∀{α β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β
                       → β ≈ β′ → Λ x α ≈ Λ y β′
  V/   : ∀{α β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β
                       → β ≈ β′ → V x α ≈ V y β′
\end{code}
For equivalence to be symmetric, the following dual form of bound variable
renaming must be derivable.
\begin{code}
  Λ/′  : ∀{α α′ β′ x y} → α ≈ α′ → y NotFreeIn α′
                        → α′ [ x / varterm y ]≡ β′ → Λ x α ≈ Λ y β′
  V/′  : ∀{α α′ β′ x y} → α ≈ α′ → y NotFreeIn α′
                        → α′ [ x / varterm y ]≡ β′ → V x α ≈ V y β′

\end{code}
It may be that the latter two rules are derivable. However, if this is so,
proving this would require several lemata which will be otherwise unnecessary.
As the goal here is to prove that equivalent formulae are equivalently
derivable, having extra constructors for equivalence will not weaken this
result.

Formula equivalence is symmetric.
\begin{code}

≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α
\end{code}
For the trivial definitions, the proof is similarly trivial.
\begin{code}
≈sym (atom r ts) = atom r ts
≈sym (α≈α′ ⇒ β≈β′) = ≈sym α≈α′ ⇒ ≈sym β≈β′
≈sym (α≈α′ ∧ β≈β′) = ≈sym α≈α′ ∧ ≈sym β≈β′
≈sym (α≈α′ ∨ β≈β′) = ≈sym α≈α′ ∨ ≈sym β≈β′
≈sym (Λ x α≈α′) = Λ x (≈sym α≈α′)
≈sym (V x α≈α′) = V x (≈sym α≈α′)
\end{code}
In the case of bound variable renaming, the dual constructor is used. If the
bound variable is being renamed with itself, then the previous trivial proof is
given instead.
\begin{code}
≈sym {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = Λ x (≈sym β≈β′)
...    | no  x≢y  = Λ/′ (≈sym β≈β′) (subNotFree (varterm x≢y) α[x/y]≡β)
                        (subInverse y∉α α[x/y]≡β)
≈sym {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = V x (≈sym β≈β′)
...    | no x≢y = V/′ (≈sym β≈β′) (subNotFree (varterm x≢y) α[x/y]≡β)
                      (subInverse y∉α α[x/y]≡β)
≈sym {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′) with varEq x y
...    | yes refl rewrite subIdentFunc α′[x/y]≡β′ = Λ x (≈sym α≈α′)
...    | no  x≢y  = Λ/ (subNotFree (varterm x≢y) α′[x/y]≡β′)
                       (subInverse y∉α′ α′[x/y]≡β′) (≈sym α≈α′)
≈sym {V x α} {V y β′} (V/′ α≈α′ y∉α′ α′[x/y]≡β′) with varEq x y
...    | yes refl rewrite subIdentFunc α′[x/y]≡β′ = V x (≈sym α≈α′)
...    | no  x≢y  = V/ (subNotFree (varterm x≢y) α′[x/y]≡β′)
                       (subInverse y∉α′ α′[x/y]≡β′) (≈sym α≈α′)

\end{code}

\todo{Is it notfree or notFree?}
\todo{Should this be in Formula?}

If a variable is not free in $\alpha$, then it should not be free in
$\alpha[x/t]$, assuming that the variable does not appear in $t$. The proof
simply comes from the definition of variable substitution and freedom for
terms.
\begin{code}

notfreeSub : ∀{α β x t z} → z NotFreeIn α → z NotInTerm t
             → α [ x / t ]≡ β → z NotFreeIn β
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

notfreeSub z∉α z∉t (ident α x)   = z∉α
notfreeSub z∉α z∉t (notfree x∉α) = z∉α
notfreeSub (atom z∉us) z∉t (atom r sub) = atom (lemma z∉us z∉t sub)
  where
    lemma : ∀{n x t z} {us vs : Vec Term n} → z NotInTerms us
                 → z NotInTerm t → [ us ][ x / t ]≡ vs → z NotInTerms vs
    lemma []           z∉t []                   = []
    lemma (z∉u ∷ z∉us) z∉t (varterm≡     ∷ sub) = z∉t ∷ lemma z∉us z∉t sub
    lemma (z∉u ∷ z∉us) z∉t (varterm≢ x≢y ∷ sub) = z∉u ∷ lemma z∉us z∉t sub
    lemma (functerm z∉ts ∷ z∉us) z∉t (functerm subts ∷ sub)
          = functerm (lemma z∉ts z∉t subts) ∷ lemma z∉us z∉t sub
notfreeSub (z∉α ⇒ z∉β) z∉t (subα ⇒ subβ) = notfreeSub z∉α z∉t subα
                                           ⇒ notfreeSub z∉β z∉t subβ
notfreeSub (z∉α ∧ z∉β) z∉t (subα ∧ subβ) = notfreeSub z∉α z∉t subα
                                           ∧ notfreeSub z∉β z∉t subβ
notfreeSub (z∉α ∨ z∉β) z∉t (subα ∨ subβ) = notfreeSub z∉α z∉t subα
                                           ∨ notfreeSub z∉β z∉t subβ
notfreeSub z∉α       z∉t (Λ∣ x α)        = z∉α
notfreeSub z∉α       z∉t (V∣ x α)        = z∉α
notfreeSub (Λ∣ x α)  z∉t (Λ x≢y y∉t sub) = Λ∣ x _
notfreeSub (V∣ x α)  z∉t (V x≢y y∉t sub) = V∣ x _
notfreeSub (Λ y z∉α) z∉t (Λ x≢y y∉t sub) = Λ y (notfreeSub z∉α z∉t sub)
notfreeSub (V y z∉α) z∉t (V x≢y y∉t sub) = V y (notfreeSub z∉α z∉t sub)

\end{code}
}

Variable freedom is preserved by formula equivalence. This is proved using the
lemma above, noting that if $z$ is bound  in $\alpha$, then it is either also
bound in $\alpha'$ or else has been renamed and so does not appear, and if $z$
does not appear in $\alpha$ then it either also does not appear in $\alpha'$ or
some bound variable has been renamed to it, so it is bound.
\begin{code}

≈notfree : ∀{α α′ z} → α ≈ α′ → z NotFreeIn α → z NotFreeIn α′
-- Proof omitted

\end{code}
\AgdaHide{
\begin{code}

--todo: is it better to split this differently?
--todo: rename variables
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
}

\subsection{Deriving the rename rule}

We want to derive the rule \inline{α ≈ α′ → Γ ⊢ α → Γ ⊢ α′}. Note that it is
the same $\Gamma$ in both deductions, so changing variable names within the
deduction of $\Gamma \vdash \alpha$ will not suffice. Instead, the deduction
tree is extended to obtain the new conclusion.

Proving this rule has a termination issue for the case that $\alpha$ is an
implication, which will be explained below. However, it is possible to prove
the stronger rule \inline{α ≈ α′ → Γ ⊢ α ↔ Γ ⊢ α′}.
\begin{code}

record _↔_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    ⟨→⟩ : A → B
    ⟨←⟩ : B → A
open _↔_

renameIff : ∀{Γ α α′} → α ≈ α′ → (Γ ⊢ α) ↔ (Γ ⊢ α′)

\end{code}
Clearly, the rename rule can be derived from \inline{renameIff}.
\begin{code}

rename      : ∀{Γ α α′}
              → α ≈ α′
              →                                Γ ⊢ α
                                              --------
              →                                Γ ⊢ α′
rename α≈α′ = ⟨→⟩ (renameIff α≈α′)
\end{code}
We prove \inline{renameIff}.
\todo{Should I show the reverse trees where the proof is omitted?}
\todo{Should I just omit all of the proofs?}

The atomic case is trivial, since an atomic formula is equivalent only to
itself.
\begin{code}
⟨→⟩ (renameIff {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts)) d = d
⟨←⟩ (renameIff {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts)) d = d
\end{code}
The remaining rules will extend the given proof tree for $\Gamma \vdash \alpha$
to obtain $\alpha'$.

The proof tree for the implication case is extended as follows.
\begin{code}

⟨→⟩ (renameIff {Γ} {α ⇒ β} {α′ ⇒ β′} (α≈α′ ⇒ β≈β′)) Γ⊢α⇒β =

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
The induction step involves invoking the rename rule on $\alpha' \approx
\alpha$ and the assumption of $\alpha'$. We have $\alpha \approx \alpha'$, and
\inline{≈sym} shows that formula equivalence is symmetric. However, calling
\inline{rename} on \inline{≈sym α≈α′} would not be structurally recursive. This
happens because Agda cannot determine that \inline{≈sym α≈α′} is structurally
smaller than \inline{α≈α′ ⇒ β≈β′}. This is the reason for proving
\inline{renameIff} instead of proving \inline{rename} directly; we have access
to a proof of $\alpha' \vdash \alpha$ by using the opposite direction of
\inline{renameIff}.
\begin{code}

  close
   (assembled-context Γ⊢α⇒β)
   (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂))
   (arrowintro α′
    (⟨→⟩ (renameIff β≈β′)
     (arrowelim
      Γ⊢α⇒β
      -- `rename (≈sym α≈α′) (assume α′)` would not be structurally recursive
      (⟨←⟩ (renameIff α≈α′)
       (assume α′)))))

\end{code}
The other direction has the same proof, with $\alpha$ swapped with $\alpha'$,
$\beta$ swapped with $\beta'$, and the opposite directions of
\inline{renameIff} used.
\todo{Show proof tree?}
\begin{code}

⟨←⟩ (renameIff {Γ} {α ⇒ β} {α′ ⇒ β′} (α≈α′ ⇒ β≈β′)) Γ⊢α′⇒β′ =
-- Proof omitted

\end{code}
\AgdaHide{
\begin{code}
  close
   (assembled-context Γ⊢α′⇒β′)
   (λ x z z₁ → z (λ z₂ z₃ → z₃ z₁ z₂))
   (arrowintro α
    (⟨←⟩ (renameIff β≈β′)
     (arrowelim
      Γ⊢α′⇒β′
      (⟨→⟩ (renameIff α≈α′)
       (assume α)))))
\end{code}
}

The proof tree for the conjunction case is extended as follows.
\begin{code}
⟨→⟩ (renameIff {Γ} {α ∧ β} {α′ ∧ β′} (α≈α′ ∧ β≈β′)) Γ⊢α∧β =
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

  close
   (assembled-context Γ⊢α∧β)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ z₃))))
   (conjelim
    Γ⊢α∧β
    (conjintro
     (⟨→⟩ (renameIff α≈α′)
      (assume α))
     (⟨→⟩ (renameIff β≈β′)
      (assume β))))

\end{code}
Again, the other direction is obtained by reversing the use of equivalences.
\begin{code}

⟨←⟩ (renameIff {Γ} {α ∧ β} {α′ ∧ β′} (α≈α′ ∧ β≈β′)) Γ⊢α′∧β′ =
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

  close
   (assembled-context Γ⊢α′∧β′)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ z₃))))
   (conjelim
    Γ⊢α′∧β′
    (conjintro
     (⟨←⟩ (renameIff α≈α′)
      (assume α′))
     (⟨←⟩ (renameIff β≈β′)
      (assume β′))))

\end{code}
}

The proof tree for the disjunction case is extended as follows.
\begin{code}

⟨→⟩ (renameIff {Γ} {α ∨ β} {α′ ∨ β′} (α≈α′ ∨ β≈β′)) Γ⊢α∨β =

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

  close
   (assembled-context Γ⊢α∨β)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
   (disjelim
    Γ⊢α∨β
    (disjintro₁ β′
     (⟨→⟩ (renameIff α≈α′)
      (assume α)))
    (disjintro₂ α′
     (⟨→⟩ (renameIff β≈β′)
      (assume β))))

\end{code}
Again, the other direction is obtained by reversing the use of equivalences.
\begin{code}

⟨←⟩ (renameIff {Γ} {α ∨ β} {α′ ∨ β′} (α≈α′ ∨ β≈β′)) Γ⊢α′∨β′ =
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

  close
   (assembled-context Γ⊢α′∨β′)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
   (disjelim
    Γ⊢α′∨β′
    (disjintro₁ β
     (⟨←⟩ (renameIff α≈α′)
      (assume α′)))
    (disjintro₂ α
     (⟨←⟩ (renameIff β≈β′)
      (assume β′))))

\end{code}
}

The first case for universal generalisation is where the bound variable is not
renamed.
\begin{code}

⟨→⟩ (renameIff {Γ} {Λ x α} {Λ .x α′} (Λ y α≈α′)) Γ⊢∀xα =

\end{code}
Since $x$ may be free $\Gamma$, we use arrow introduction and elimination so
that $\Gamma$ is not assumed when the universal generalisation re-introduced.

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

  close
   (assembled-context Γ⊢∀xα)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro x (all⟨ Λ∣ x α ⟩)
      (⟨→⟩ (renameIff α≈α′)
       (univelim (varterm x) (ident α x)
        (assume (Λ x α))))))
    Γ⊢∀xα)

\end{code}
Again, the other direction is obtained by reversing the use of equivalences.
\begin{code}

⟨←⟩ (renameIff {Γ} {Λ x α} {Λ .x α′} (Λ y α≈α′)) Γ⊢∀xα′ =
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

  close
   (assembled-context Γ⊢∀xα′)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α′)
     (univintro x (all⟨ Λ∣ x α′ ⟩)
      (⟨←⟩ (renameIff α≈α′)
       (univelim (varterm x) (ident α′ x)
        (assume (Λ x α′))))))
    Γ⊢∀xα′)
\end{code}
}

The second case for universal generalisation renames the bound variable, then
follows another equivalence.
\todo{wording}
\begin{code}

⟨→⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′)) Γ⊢∀xα =

\end{code}
Since $x$ is being renamed to $y$, we know $y$ is not free in $\alpha$, and so
it is also not free in $\forall x \alpha$. We have $\beta \coloneq \alpha[x/y]$.
\begin{prooftree}
  \AxiomC{[$\forall x \alpha$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\beta$}
  \RightLabel{induction}
  \UnaryInfC{$\beta'$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall y \beta$}
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall x \alpha \rightarrow \forall y \beta'$}
      \AxiomC{$\Gamma$}
      \UnaryInfC{$\vdots$}
      \UnaryInfC{$\forall x \alpha$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\forall y \beta'$}
\end{prooftree}
\begin{code}

  close
   (assembled-context Γ⊢∀xα)
   (λ x₁ z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro y all⟨ Λ x y∉α ⟩
      (⟨→⟩ (renameIff β≈β′)
       (univelim (varterm y) α[x/y]≡β
        (assume (Λ x α))))))
    Γ⊢∀xα)

\end{code}
The other direction varies depending on if $x$ is equal to $y$.
\begin{code}

⟨←⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′)) Γ⊢∀yβ′
    with varEq x y

\end{code}
In the degenerate case where $x = y$, we have $\beta = \alpha$.
\begin{prooftree}
  \AxiomC{[$\forall x \beta'$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\beta'$}
  \RightLabel{induction}
  \UnaryInfC{$\alpha$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall x \alpha$}
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall x \beta' \rightarrow \forall x \alpha$}
      \AxiomC{$\Gamma$}
      \UnaryInfC{$\vdots$}
      \UnaryInfC{$\forall x \beta'$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\forall x \alpha$}
\end{prooftree}
\begin{code}

... | yes refl rewrite subIdentFunc α[x/y]≡β =
  close
   (assembled-context Γ⊢∀yβ′)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x β′)
     (univintro x all⟨ Λ∣ x β′ ⟩
      (⟨←⟩ (renameIff β≈β′)
       (univelim (varterm x) (ident β′ x)
        (assume (Λ x β′))))))
    Γ⊢∀yβ′)

\end{code}
Otherwise, $\beta[y/x] = \alpha$, and $x$ is not free in $\forall y \beta'$
because $x$ is not free in $\beta$, since $\beta$ is obtained by substituting
$x$ with $y$ in $\alpha$.
\begin{prooftree}
  \AxiomC{[$\forall y \beta'$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\beta'$}
  \RightLabel{induction}
  \UnaryInfC{$\beta$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall y \beta$}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\alpha$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall x \alpha$}
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall x \beta' \rightarrow \forall x \alpha$}
      \AxiomC{$\Gamma$}
      \UnaryInfC{$\vdots$}
      \UnaryInfC{$\forall y \beta'$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\forall x \alpha$}
\end{prooftree}
\begin{code}

... | no  x≢y  =
  close
   (assembled-context Γ⊢∀yβ′)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ y β′)
     (univintro x all⟨ Λ y (≈notfree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β)) ⟩
      (univelim (varterm x) (subInverse y∉α α[x/y]≡β)
       (univintro y all⟨ Λ∣ y β′ ⟩
        (⟨←⟩ (renameIff β≈β′)
         (univelim (varterm y) (ident β′ y)
          (assume (Λ y β′))))))))
    Γ⊢∀yβ′)

\end{code}

The third case is the dual of the second.
\begin{code}

⟨→⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′)) Γ⊢∀xα =

\end{code}
Note that $\beta' \coloneq \alpha'[x/y]$.
\begin{prooftree}
  \AxiomC{[$\forall x \alpha$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\alpha$}
  \RightLabel{induction}
  \UnaryInfC{$\alpha'$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall x \alpha'$}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\beta'$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall y \beta'$}
      \AxiomC{$\Gamma$}
      \UnaryInfC{$\vdots$}
      \UnaryInfC{$\forall x \alpha$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\forall y \beta'$}
\end{prooftree}
\begin{code}

  close
   (assembled-context Γ⊢∀xα)
   (λ x₁ z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x α)
     (univintro y all⟨ ≈notfree (Λ x (≈sym α≈α′)) (Λ x y∉α′) ⟩
      (univelim (varterm y) α′[x/y]≡β′
       (univintro x all⟨ Λ∣ x α ⟩
        (⟨→⟩ (renameIff α≈α′)
         (univelim (varterm x) (ident α x)
          (assume (Λ x α))))))))
    Γ⊢∀xα)

\end{code}
The other direction varies depending on if $x$ is equal to $y$.
\begin{code}

⟨←⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′)) Γ⊢∀yβ′
    with varEq x y

\end{code}
In the degenerate case where $x = y$, we have $\alpha' = \beta'$.
\begin{prooftree}
  \AxiomC{[$\forall x \beta'$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\beta'$}
  \RightLabel{induction}
  \UnaryInfC{$\alpha$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall x \alpha$}
      \AxiomC{$\Gamma$}
      \UnaryInfC{$\vdots$}
      \UnaryInfC{$\forall x \beta'$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\forall x \alpha$}
\end{prooftree}
\begin{code}

... | yes refl rewrite subIdentFunc α′[x/y]≡β′ =
  close
   (assembled-context Γ⊢∀yβ′)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ x β′)
     (univintro x all⟨ Λ∣ x β′ ⟩ -- Only difference
      (⟨←⟩ (renameIff α≈α′)
       (univelim (varterm x) (ident β′ x)
        (assume (Λ x β′))))))
    Γ⊢∀yβ′)

\end{code}
Otherwise, $\beta'[y/x] = \alpha'$, and $x$ is not free in $\forall y \beta'$
since $\beta'$ has been obtained by substituting $x$ with $y$ in $\alpha'$.
\begin{prooftree}
  \AxiomC{[$\forall y \beta'$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\alpha'$}
  \RightLabel{induction}
  \UnaryInfC{$\alpha$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall x \alpha$}
      \AxiomC{$\Gamma$}
      \UnaryInfC{$\vdots$}
      \UnaryInfC{$\forall y \beta'$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\forall x \alpha$}
\end{prooftree}
\begin{code}

... | no  x≢y  =
  close
   (assembled-context Γ⊢∀yβ′)
   (λ x z → z (λ z₁ → z₁ (λ z₂ → z₂)))
   (arrowelim
    (arrowintro (Λ y β′)
     (univintro x all⟨ Λ y (subNotFree (varterm x≢y) α′[x/y]≡β′) ⟩
      (⟨←⟩ (renameIff α≈α′)
       (univelim (varterm x) (subInverse y∉α′ α′[x/y]≡β′)
        (assume (Λ y β′))))))
    Γ⊢∀yβ′)

\end{code}

Finally, we examine the existential generalisation cases. The first case is
where the bound variable is not renamed.
\begin{code}

⟨→⟩ (renameIff {Γ} {V x α} {V .x α′} (V y α≈α′)) Γ⊢∃xα =

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

  close
   (assembled-context Γ⊢∃xα)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x α′ ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    Γ⊢∃xα
    (existintro (varterm x) x (ident α′ x)
     (⟨→⟩ (renameIff α≈α′)
      (assume α))))

\end{code}
The reverse direction is the same, with equivalences reversed.
\begin{code}

⟨←⟩ (renameIff {Γ} {V x α} {V .x α′} (V y α≈α′)) Γ⊢∃xα′ =
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

  close
   (assembled-context Γ⊢∃xα′)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    Γ⊢∃xα′
    (existintro (varterm x) x (ident α x)
     (⟨←⟩ (renameIff α≈α′)
      (assume α′))))

\end{code}
}

The second case for existential generalisation renames the bound variable, then
follows another equivalence. The proof depends on whether $x$ is equal to $y$.
\begin{code}

⟨→⟩ (renameIff {Γ} {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′)) Γ⊢∃xα
    with varEq x y

\end{code}
Since $\beta = \alpha[x/y]$, we have $\alpha = \beta[y/x]$. If $x \neq y$, then
$x$ cannot be free in $\beta$, and so it is also not free in $\exists y \beta$.
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\exists x \alpha$}
    \AxiomC{[$\alpha$]}
    \RightLabel{$\exists^+$}
    \UnaryInfC{$\exists y \beta$}
        \AxiomC{[$\beta$]}
        \RightLabel{induction}
        \UnaryInfC{$\beta'$}
        \RightLabel{$\exists^+$}
        \UnaryInfC{$\exists y \beta'$}
      \RightLabel{$\exists^-$}
      \BinaryInfC{$\exists y \beta'$}
    \RightLabel{$\exists^-$}
    \BinaryInfC{$\exists y \beta'$}
\end{prooftree}
\begin{code}

... | no  x≢y  =
  close
   (assembled-context Γ⊢∃xα)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ z₃ (λ z₅ → z₅ (λ z₆ → z₆)))))
   (existelim (all⟨ V y (≈notfree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β)) ⟩
               all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- all⟨- [ refl ] ⟩))))
    Γ⊢∃xα
    (existelim (all⟨ V∣ y β′ ⟩ all∪ (all- all⟨- [ refl ] ⟩))
     (existintro (varterm x) y (subInverse y∉α α[x/y]≡β)
      (assume α))
     (existintro (varterm y) y (ident β′ y)
      (⟨→⟩ (renameIff β≈β′) -- Not structurally recursive
       (assume _)))))

\end{code}
In the degenerate case, we have $\beta = \alpha$.
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\exists x \alpha$}
      \AxiomC{[$\alpha$]}
      \RightLabel{induction}
      \UnaryInfC{$\beta'$}
      \RightLabel{$\exists^+$}
      \UnaryInfC{$\exists x \beta'$}
    \RightLabel{$\exists^-$}
    \BinaryInfC{$\exists x \beta'$}
\end{prooftree}
\begin{code}

... | yes refl with subIdentFunc α[x/y]≡β
...            | refl =
  close
   (assembled-context Γ⊢∃xα)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β′ ⟩ all∪ (all- all⟨ y∉α ⟩))
    Γ⊢∃xα
    (existintro (varterm x) x (ident β′ x)
     (⟨→⟩ (renameIff β≈β′)
      (assume α))))

\end{code}
Now, consider the other direction.
\begin{code}

⟨←⟩ (renameIff {Γ} {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′)) Γ⊢∃yβ′ =

\end{code}
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\exists y \beta'$}
      \AxiomC{[$\beta'$]}
      \RightLabel{induction}
      \UnaryInfC{$\beta$}
      \RightLabel{$\exists^+$}
      \UnaryInfC{$\exists x \alpha$}
    \RightLabel{$\exists^-$}
    \BinaryInfC{$\exists x \alpha$}
\end{prooftree}
\begin{code}

  close
   (assembled-context Γ⊢∃yβ′)
   (λ x₁ x₂ x₃ → x₂ x₃ λ x₄ → x₄ λ x₅ → x₅)
   (existelim (all⟨ V x y∉α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    Γ⊢∃yβ′
    (existintro (varterm y) x α[x/y]≡β
     (⟨←⟩ (renameIff β≈β′)
      (assume β′))))

\end{code}

The third case is the dual of the second.
\begin{code}

⟨→⟩ (renameIff {Γ} {V x α} {V y β} (V/′ α≈α′ y∉α′ α′[x/y]≡β′)) Γ⊢∃xα
    with varEq x y

\end{code}
If $x = y$, then $\alpha' = \beta'$.
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\exists x \alpha$}
      \AxiomC{[$\alpha$]}
      \RightLabel{induction}
      \UnaryInfC{$\beta'$}
      \RightLabel{$\exists^+$}
      \UnaryInfC{$\exists x \beta'$}
    \RightLabel{$\exists^-$}
    \BinaryInfC{$\exists x \beta'$}
\end{prooftree}
\begin{code}

... | yes refl rewrite subIdentFunc α′[x/y]≡β′ =
  close
   (assembled-context Γ⊢∃xα)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V∣ x β ⟩ all∪ (all- all⟨- [ refl ] ⟩)) -- Differs here
    Γ⊢∃xα
    (existintro (varterm x) x (ident β x) -- And here
     (⟨→⟩ (renameIff α≈α′)
      (assume α))))

\end{code}
Otherwise, because $\alpha'[x/y] = \beta'$, we have $\alpha' = \beta'[y/x]$,
and $x$ is not free in $\beta'$, and so is not free in $\exists y \beta'$.
\todo{Remark that the dual suits $\exists$, the  other suits $\forall$?}
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\exists x \alpha$}
      \AxiomC{[$\alpha$]}
      \RightLabel{induction}
      \UnaryInfC{$\alpha'$}
      \RightLabel{$\exists^+$}
      \UnaryInfC{$\exists y \beta'$}
    \RightLabel{$\exists^-$}
    \BinaryInfC{$\exists y \beta'$}
\end{prooftree}
\begin{code}

... | no x≢y   =
  close
   (assembled-context Γ⊢∃xα)
   (λ x₁ z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ → z₃)))
   (existelim (all⟨ V y (subNotFree (varterm x≢y) α′[x/y]≡β′) ⟩
               all∪ (all- all⟨- [ refl ] ⟩)) -- Differs here
    Γ⊢∃xα
    (existintro (varterm x) y (subInverse y∉α′ α′[x/y]≡β′) -- And here
     (⟨→⟩ (renameIff α≈α′)
      (assume α))))

\end{code}
Consider the other direction.
\begin{code}

⟨←⟩ (renameIff {Γ} {V x α} {V y β′} (V/′ α≈α′ y∉α′ α′[x/y]≡β′)) Γ⊢∃yβ′ =

\end{code}
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \UnaryInfC{$\vdots$}
  \UnaryInfC{$\exists y \beta'$}
    \AxiomC{[$\beta'$]}
    \RightLabel{$\exists^+$}
    \UnaryInfC{$\exists x \alpha'$}
        \AxiomC{[$\alpha'$]}
        \RightLabel{induction}
        \UnaryInfC{$\alpha$}
        \RightLabel{$\exists^+$}
        \UnaryInfC{$\exists x \alpha$}
      \RightLabel{$\exists^-$}
      \BinaryInfC{$\exists x \alpha$}
    \RightLabel{$\exists^-$}
    \BinaryInfC{$\exists x \alpha$}
\end{prooftree}
\begin{code}

  close
   (assembled-context Γ⊢∃yβ′)
   (λ x z z₁ → z z₁ (λ z₂ → z₂ (λ z₃ z₄ → z₄ z₃ (λ z₅ → z₅ (λ z₆ → z₆)))))
   (existelim (all⟨ V x (≈notfree (≈sym α≈α′) y∉α′) ⟩
               all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- all⟨ y∉α′ ⟩))))
    Γ⊢∃yβ′
    (existelim (all⟨ V∣ x α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
     (existintro (varterm y) x α′[x/y]≡β′
      (assume β′))
     (existintro (varterm x) x (ident α x)
      (⟨←⟩ (renameIff α≈α′)
       (assume _)))))

\end{code}

We can conclude that examining formulae only on an intensional level does not
restrict the deductive power of the system.
