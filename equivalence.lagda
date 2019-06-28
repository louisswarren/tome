Avoiding conflicts of variables with the same name can be done algorithmically
by machines (including internally by Agda) by using a nameless notation
\citep{debruijin1972}. Since natural deduction is intended to be used by
humans, treatments such as that of \citet{schwichtenberg} state that formulae
can be used equivalently if they are equivalent up to renaming of bound
variables. This has not been included in the definition of formulae or of
natural deduction. To do so would introduce an extra complication to the
deduction rules, as every step in a natural deduction proof would have to
include a proof that the conclusion is equivalent to the desired one. However,
it is possible to prove that this is unnecessary; in the system given, if
$\Gamma \vdash \alpha$, and $\alpha$ is equivalent to $\alpha'$ up to the
renaming of bound variables, then $\Gamma \vdash \alpha'$.

\begin{code}

\end{code}
\AgdaHide{
\begin{code}

open import Decidable
open import Deduction
open import Ensemble
open import Formula
open import List
open import Vec

\end{code}
}

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
proving this would require several lemmas which will be otherwise unnecessary.
As the goal here is to prove that equivalent formulae are equivalently
derivable, having extra constructors for equivalence will not weaken this
result. It will be shown later that it would be more `natural' to adopt the
rules \inline{Λ/} and \inline{V/′} and to derive \inline{Λ/′} and \inline{V/}
if possible.

\begin{lemma}
Formula equivalence is symmetric.
\end{lemma}
\begin{proof}
$ $
\begin{code}

≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α
\end{code}
For the trivial definitions, the proof is similarly trivial.
\begin{code}
≈sym (atom r ts)   = atom r ts
≈sym (α≈α′ ⇒ β≈β′) = ≈sym α≈α′ ⇒ ≈sym β≈β′
≈sym (α≈α′ ∧ β≈β′) = ≈sym α≈α′ ∧ ≈sym β≈β′
≈sym (α≈α′ ∨ β≈β′) = ≈sym α≈α′ ∨ ≈sym β≈β′
≈sym (Λ x α≈α′)    = Λ x (≈sym α≈α′)
≈sym (V x α≈α′)    = V x (≈sym α≈α′)
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
...    | no  x≢y  = V/′ (≈sym β≈β′) (subNotFree (varterm x≢y) α[x/y]≡β)
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
\codeqed
\end{proof}

If a variable is not free in $\alpha$, then it should not be free in
$\alpha[x/t]$, assuming that the variable does not appear in $t$. The proof
simply comes from the definition of variable substitution and freedom for
terms.
\begin{code}

notFreeSub : ∀{α β x t z} → z NotFreeIn α → z NotInTerm t
             → α [ x / t ]≡ β → z NotFreeIn β
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

notFreeSub z∉α z∉t (ident α x)   = z∉α
notFreeSub z∉α z∉t (notfree x∉α) = z∉α
notFreeSub (atom z∉us) z∉t (atom r sub) = atom (lemma z∉us z∉t sub)
  where
    lemma : ∀{n x t z} {us vs : Vec Term n} → z NotInTerms us
                 → z NotInTerm t → [ us ][ x / t ]≡ vs → z NotInTerms vs
    lemma []           z∉t []                   = []
    lemma (z∉u ∷ z∉us) z∉t (varterm≡     ∷ sub) = z∉t ∷ lemma z∉us z∉t sub
    lemma (z∉u ∷ z∉us) z∉t (varterm≢ x≢y ∷ sub) = z∉u ∷ lemma z∉us z∉t sub
    lemma (functerm z∉ts ∷ z∉us) z∉t (functerm subts ∷ sub)
          = functerm (lemma z∉ts z∉t subts) ∷ lemma z∉us z∉t sub
notFreeSub (z∉α ⇒ z∉β) z∉t (subα ⇒ subβ) = notFreeSub z∉α z∉t subα
                                           ⇒ notFreeSub z∉β z∉t subβ
notFreeSub (z∉α ∧ z∉β) z∉t (subα ∧ subβ) = notFreeSub z∉α z∉t subα
                                           ∧ notFreeSub z∉β z∉t subβ
notFreeSub (z∉α ∨ z∉β) z∉t (subα ∨ subβ) = notFreeSub z∉α z∉t subα
                                           ∨ notFreeSub z∉β z∉t subβ
notFreeSub z∉α       z∉t (Λ↓ x α)        = z∉α
notFreeSub z∉α       z∉t (V↓ x α)        = z∉α
notFreeSub (Λ↓ x α)  z∉t (Λ x≢y y∉t sub) = Λ↓ x _
notFreeSub (V↓ x α)  z∉t (V x≢y y∉t sub) = V↓ x _
notFreeSub (Λ y z∉α) z∉t (Λ x≢y y∉t sub) = Λ y (notFreeSub z∉α z∉t sub)
notFreeSub (V y z∉α) z∉t (V x≢y y∉t sub) = V y (notFreeSub z∉α z∉t sub)

\end{code}
}

Variable freedom is preserved by formula equivalence. This is proved using the
lemma above, noting that if $z$ is bound  in $\alpha$, then it is either also
bound in $\alpha'$ or else has been renamed and so does not appear, and if $z$
does not appear in $\alpha$ then it either also does not appear in $\alpha'$ or
some bound variable has been renamed to it, so it is bound.
\begin{code}

≈notFree : ∀{α α′ z} → α ≈ α′ → z NotFreeIn α → z NotFreeIn α′
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

≈notFree (atom r ts) (atom z∉ts) = atom z∉ts
≈notFree (α≈α′ ⇒ β≈β′) (z∉α ⇒ z∉β) = ≈notFree α≈α′ z∉α ⇒ ≈notFree β≈β′ z∉β
≈notFree (α≈α′ ∧ β≈β′) (z∉α ∧ z∉β) = ≈notFree α≈α′ z∉α ∧ ≈notFree β≈β′ z∉β
≈notFree (α≈α′ ∨ β≈β′) (z∉α ∨ z∉β) = ≈notFree α≈α′ z∉α ∨ ≈notFree β≈β′ z∉β
≈notFree (Λ x α≈α′) (Λ↓ .x α) = Λ↓ x _
≈notFree (V x α≈α′) (V↓ .x α) = V↓ x _
≈notFree {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′) (Λ↓ .x α) with varEq x y
...    | yes refl = Λ↓ x β′
...    | no  x≢y  = Λ y (≈notFree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β))
≈notFree {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′) (V↓ .x α) with varEq x y
...    | yes refl = V↓ x β′
...    | no  x≢y  = V y (≈notFree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β))
≈notFree {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′) (Λ↓ x α) with varEq x y
...    | yes refl = Λ↓ x β′
...    | no  x≢y  = Λ y (subNotFree (varterm x≢y) α′[x/y]≡β′)
≈notFree {V x α} {V y β′} (V/′ α≈α′ y∉α′ α′[x/y]≡β′) (V↓ x α) with varEq x y
...    | yes refl = V↓ x β′
...    | no  x≢y  = V y (subNotFree (varterm x≢y) α′[x/y]≡β′)
≈notFree (Λ y α≈α′) (Λ .y z∉α) = Λ y (≈notFree α≈α′ z∉α)
≈notFree (V y α≈α′) (V .y z∉α) = V y (≈notFree α≈α′ z∉α)
≈notFree {Λ x α} {Λ y β′} {z} (Λ/ y∉α α[x/y]≡β β≈β′) (Λ .x z∉α) with varEq z y
...    | yes refl = Λ↓ z β′
...    | no  z≢y  = Λ y (≈notFree β≈β′ (notFreeSub z∉α (varterm z≢y) α[x/y]≡β))
≈notFree {V x α} {V y β′} {z} (V/ y∉α α[x/y]≡β β≈β′) (V .x z∉α) with varEq z y
...    | yes refl = V↓ z β′
...    | no  z≢y  = V y (≈notFree β≈β′ (notFreeSub z∉α (varterm z≢y) α[x/y]≡β))
≈notFree {Λ x α} {Λ y β′} {z} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β) (Λ .x z∉α) with varEq z y
...    | yes refl = Λ↓ z β′
...    | no  z≢y  = Λ y (notFreeSub (≈notFree α≈α′ z∉α) (varterm z≢y) α′[x/y]≡β)
≈notFree {V x α} {V y β′} {z} (V/′ α≈α′ y∉α′ α′[x/y]≡β) (V .x z∉α) with varEq z y
...    | yes refl = V↓ z β′
...    | no  z≢y  = V y (notFreeSub (≈notFree α≈α′ z∉α) (varterm z≢y) α′[x/y]≡β)

\end{code}
}

\subsection{Deriving the rename rule}

We want to derive the deduction rule $\alpha \approx \alpha' \rightarrow \Gamma
\vdash \alpha \rightarrow \Gamma \vdash \alpha'$. As $\Gamma$ is the same in
both deductions, changing variable names within the deduction of $\Gamma \vdash
\alpha$ will not suffice. Instead, the deduction tree is extended to obtain the
new conclusion.

Proving this rule has a termination issue for the case that $\alpha$ is an
implication, which will be explained below. However, it is possible to prove
the stronger rule $\alpha \approx \alpha' \rightarrow (\Gamma \vdash \alpha
\leftrightarrow \Gamma \vdash \alpha')$. A simplified notion of
`$\leftrightarrow$' in Agda can be defined as follows.\footnote{
This is simplified in that it requires all types involved to be of type
\inline{Set₁}, which is enough for our purposes.}
\begin{code}

private
  record _↔_ (A : Set₁) (B : Set₁) : Set₁ where
    field
      ⟨→⟩ : A → B
      ⟨←⟩ : B → A
  open _↔_

\end{code}
We can now define the stronger rename rule.
\begin{code}

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
It remains to prove \inline{renameIff}. In the natural deduction proofs that
follow, the subset proofs for \inline{close} were found automatically by Agda's
proof search. The variable freedom proofs were also found, except where extra
reasoning (regarding substitution and equivalence lemmas) were required. Such
lemmas are necessary when manipulating proof trees in the abstract.
\begin{proof}
The atomic case is trivial, since an atomic formula is equivalent only to
itself.
\begin{code}
⟨→⟩ (renameIff {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts)) d = d
⟨←⟩ (renameIff {Γ} {atom r ts} {.(atom r ts)} (atom .r .ts)) d = d
\end{code}

The proof tree for the implication case is extended as follows.
\begin{code}

⟨→⟩ (renameIff {Γ} {α ⇒ β} {α′ ⇒ β′} (α≈α′ ⇒ β≈β′)) Γ⊢α⇒β =

\end{code}
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \noLine\UnaryInfC{$\vdots$}\noLine
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
One of the induction steps involves invoking the rename rule on $\alpha' \approx
\alpha$ and the assumption of $\alpha'$. We have $\alpha \approx \alpha'$, and
\inline{≈sym} shows that formula equivalence is symmetric. However, calling
\inline{rename} on \inline{≈sym α≈α′} would not be structurally recursive,
because Agda cannot determine that \inline{≈sym α≈α′} is structurally smaller
than \inline{α≈α′ ⇒ β≈β′}. This is the reason for proving \inline{renameIff}
instead of proving \inline{rename} directly; we have access to a proof of
$\alpha' \vdash \alpha$ by using the opposite direction of \inline{renameIff}.
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
\begin{code}

⟨←⟩ (renameIff {Γ} {α ⇒ β} {α′ ⇒ β′} (α≈α′ ⇒ β≈β′)) Γ⊢α′⇒β′ =
-- Proof omitted.

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
  \noLine\UnaryInfC{$\vdots$}\noLine
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
  \noLine\UnaryInfC{$\vdots$}\noLine
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
   (λ x z z₁
    → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
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
   (λ x z z₁
    → z z₁ (λ z₂ → z₂ (λ z₃ → z₃ (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ → z₄))))
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
that $\Gamma$ is not assumed when the universal generalisation is re-introduced.

\begin{prooftree}
  \AxiomC{[$\forall x \alpha$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\alpha$}
  \RightLabel{induction}
  \UnaryInfC{$\alpha'$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall x \alpha'$}
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall x \alpha \rightarrow \forall x \alpha'$}
      \AxiomC{$\Gamma$}
      \noLine\UnaryInfC{$\vdots$}\noLine
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
     (univintro x (all⟨ Λ↓ x α ⟩)
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
     (univintro x (all⟨ Λ↓ x α′ ⟩)
      (⟨←⟩ (renameIff α≈α′)
       (univelim (varterm x) (ident α′ x)
        (assume (Λ x α′))))))
    Γ⊢∀xα′)
\end{code}
}

The second case for universal generalisation renames the bound variable, then
follows another equivalence.
\begin{code}

⟨→⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′)) Γ⊢∀xα =

\end{code}
Since $x$ is being renamed to $y$, we know $y$ is not free in $\alpha$, and so
it is also not free in $\forall x \alpha$. Define $\beta \coloneq \alpha[x/y]$.
\begin{prooftree}
  \AxiomC{[$\forall x \alpha$]}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\beta$}
  \RightLabel{induction}
  \UnaryInfC{$\beta'$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall y \beta'$}
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall x \alpha \rightarrow \forall y \beta'$}
      \AxiomC{$\Gamma$}
      \noLine\UnaryInfC{$\vdots$}\noLine
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
      \noLine\UnaryInfC{$\vdots$}\noLine
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
     (univintro x all⟨ Λ↓ x β′ ⟩
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
  \UnaryInfC{$\forall y \beta' \rightarrow \forall x \alpha$}
      \AxiomC{$\Gamma$}
      \noLine\UnaryInfC{$\vdots$}\noLine
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
     (univintro x
      all⟨ Λ y (≈notFree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β)) ⟩
      (univelim (varterm x) (subInverse y∉α α[x/y]≡β)
       (univintro y all⟨ Λ↓ y β′ ⟩
        (⟨←⟩ (renameIff β≈β′)
         (univelim (varterm y) (ident β′ y)
          (assume (Λ y β′))))))))
    Γ⊢∀yβ′)

\end{code}

The third case is the dual of the second.
\begin{code}

⟨→⟩ (renameIff {Γ} {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′)) Γ⊢∀xα =

\end{code}
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
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall x \alpha \rightarrow \forall y \beta'$}
      \AxiomC{$\Gamma$}
      \noLine\UnaryInfC{$\vdots$}\noLine
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
     (univintro y all⟨ ≈notFree (Λ x (≈sym α≈α′)) (Λ x y∉α′) ⟩
      (univelim (varterm y) α′[x/y]≡β′
       (univintro x all⟨ Λ↓ x α ⟩
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
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall x \beta' \rightarrow \forall x \alpha$}
      \AxiomC{$\Gamma$}
      \noLine\UnaryInfC{$\vdots$}\noLine
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
     (univintro x all⟨ Λ↓ x β′ ⟩
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
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\forall y \beta' \rightarrow \forall x \alpha$}
      \AxiomC{$\Gamma$}
      \noLine\UnaryInfC{$\vdots$}\noLine
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
  \noLine\UnaryInfC{$\vdots$}\noLine
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
   (existelim (all⟨ V↓ x α′ ⟩ all∪ (all- all⟨- [ refl ] ⟩))
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
   (existelim (all⟨ V↓ x α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
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
  \noLine\UnaryInfC{$\vdots$}\noLine
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
   (existelim (all⟨ V y (≈notFree β≈β′ (subNotFree (varterm x≢y) α[x/y]≡β)) ⟩
               all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- all⟨- [ refl ] ⟩))))
    Γ⊢∃xα
    (existelim (all⟨ V↓ y β′ ⟩ all∪ (all- all⟨- [ refl ] ⟩))
     (existintro (varterm x) y (subInverse y∉α α[x/y]≡β)
      (assume α))
     (existintro (varterm y) y (ident β′ y)
      (⟨→⟩ (renameIff β≈β′)
       (assume _)))))

\end{code}
In the degenerate case, we have $\beta = \alpha$.
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \noLine\UnaryInfC{$\vdots$}\noLine
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
   (existelim (all⟨ V↓ x β′ ⟩ all∪ (all- all⟨ y∉α ⟩))
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
  \noLine\UnaryInfC{$\vdots$}\noLine
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
  \noLine\UnaryInfC{$\vdots$}\noLine
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
   (existelim (all⟨ V↓ x β ⟩ all∪ (all- all⟨- [ refl ] ⟩))
    Γ⊢∃xα
    (existintro (varterm x) x (ident β x)
     (⟨→⟩ (renameIff α≈α′)
      (assume α))))

\end{code}
Otherwise, because $\alpha'[x/y] = \beta'$, we have $\alpha' = \beta'[y/x]$,
and $x$ is not free in $\beta'$, and so is not free in $\exists y \beta'$.
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \noLine\UnaryInfC{$\vdots$}\noLine
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
               all∪ (all- all⟨- [ refl ] ⟩))
    Γ⊢∃xα
    (existintro (varterm x) y (subInverse y∉α′ α′[x/y]≡β′)
     (⟨→⟩ (renameIff α≈α′)
      (assume α))))

\end{code}
Consider the other direction.
\begin{code}

⟨←⟩ (renameIff {Γ} {V x α} {V y β′} (V/′ α≈α′ y∉α′ α′[x/y]≡β′)) Γ⊢∃yβ′ =

\end{code}
\begin{prooftree}
  \AxiomC{$\Gamma$}
  \noLine\UnaryInfC{$\vdots$}\noLine
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
   (existelim (all⟨ V x (≈notFree (≈sym α≈α′) y∉α′) ⟩
               all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- all⟨ y∉α′ ⟩))))
    Γ⊢∃yβ′
    (existelim (all⟨ V↓ x α ⟩ all∪ (all- all⟨- [ refl ] ⟩))
     (existintro (varterm y) x α′[x/y]≡β′
      (assume β′))
     (existintro (varterm x) x (ident α x)
      (⟨←⟩ (renameIff α≈α′)
       (assume _)))))

\end{code}
\codeqed
\end{proof}

We can conclude that examining formulae only on an intensional level does not
restrict the deductive power of the system.

There is a dual structure in the proofs above, in the quantifier cases where
the bound variable is renamed. Some proofs are straightforward in that they
eliminate the quantifier, insert the derivation of the equivalent subcomponent
by induction, then reintroduce the quantifier. Others are more complex, in that
require an extra introduction and elimination step. The straightforward proofs
are for the forward direction for \inline{Λ/} and \inline{V/′}, and the reverse
direction for \inline{Λ/′} and \inline{V/}, while the complex proofs are the
forward direction for \inline{Λ/′} and \inline{V/}, and the reverse direction
for \inline{Λ/} and \inline{V/′}. Since the forward direction of each of these
rules is the same as the reverse direction of its dual, we see that it would be
simplest to do renaming with the rules \inline{Λ/} and \inline{V/′}, and have
\inline{Λ/′} and \inline{V/} be the derived rules, if possible.
