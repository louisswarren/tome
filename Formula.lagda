\AgdaHide{
\begin{code}

module Formula where

\end{code}
}
\begin{code}

open import Agda.Builtin.Sigma

\end{code}
\AgdaHide{
\begin{code}

open import Decidable
open import Nat
open import Vec

\end{code}
}

\subsection{Basic definitions}

We adopt the definitions of \citet{schwichtenberg}.

There are countably many variables, and there are countably many function
symbols of each (natural) arity. Constants are functions with arity zero.
Function symbols of different arities with the same index are considered
distinct.
\begin{code}

record Variable : Set where
  constructor var
  field
    idx : ℕ

open Variable renaming (idx to varidx)

record Function : Set where
  constructor func
  field
    idx   : ℕ
    arity : ℕ

open Function renaming (idx to funcidx ; arity to funcarity)

\end{code}
By defining these as \inline{record} types, we get destructors for accessing
the indices and arities, which we then extract into the current module for ease
of use. Note that the indices are natural numbers. While it seems equivalent
and more useful to use string indices, strings are not supported by Agda's
proof search. Internally, strings are not recursively defined as the natural
numbers are; instead the string type is a postulated type which is bound to
string literals.

Terms are either variables, or functions applied to the appropriate number of
arguments (zero for constants).
\begin{code}

data Term : Set where
  varterm  : (x : Variable) → Term
  functerm : (f : Function) → (ts : Vec Term (funcarity f)) → Term

\end{code}

Relation symbols work the same way as function symbols.
\begin{code}

record Relation : Set where
  constructor rel
  field
    idx   : ℕ
    arity : ℕ

open Relation renaming (idx to relidx ; arity to relarity)

\end{code}

A formula is either atomic (a prime formula), or formed from one of the logical
connectives or quantifiers. We use `\inline{Λ}' (capital lambda) and
`\inline{V}' (capital `v') for `$\forall$' and `$\exists$', since `\inline{∀}'
is reserved by Agda\footnote{
  While the typical n-ary logical operator symbols `\inline{⋁}' and
  `\inline{⋀}' are available, they are more easily confused with the symbols
  `\inline{∧}' and `\inline{∨}' for `and' and `or', and are unavailable in some
  fonts.}.

\begin{code}

data Formula : Set where
  atom   : (r : Relation) → (ts : Vec Term (relarity r)) → Formula
  _⇒_    : (α : Formula)  → (β : Formula) → Formula
  _∧_    : (α : Formula)  → (β : Formula) → Formula
  _∨_    : (α : Formula)  → (β : Formula) → Formula
  Λ      : (x : Variable) → (α : Formula) → Formula
  V      : (x : Variable) → (α : Formula) → Formula

_⇔_ : Formula → Formula → Formula
Φ ⇔ Ψ = (Φ ⇒ Ψ) ∧ (Ψ ⇒ Φ)

\end{code}
The logical connectives are right-associative, and have the usual order of
precedence.
\begin{code}

infixr 105 _⇒_ _⇔_
infixr 106 _∨_
infixr 107 _∧_

\end{code}

Equality of formulae is decidable. Logically, this follows from the fact that
formulae are inductively defined. The proof is obtained by case analysis, using
lemmas on the types used to construct formulae. As these proofs are
unremarkable, and follow the same pattern as the proof for decidable equality
of natural numbers above, they are omitted.
\begin{code}

varEq : Decidable≡ Variable
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

varEq (var n) (var m) with natEq n m
...                   | yes refl = yes refl
...                   | no  n≢m  = no λ { refl → n≢m refl }

\end{code}
}
\begin{code}

relEq : Decidable≡ Relation
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

relEq (rel n j) (rel m k) with natEq n m
...                       | no  n≢m  = no λ { refl → n≢m refl }
...                       | yes refl with natEq j k
...                                  | yes refl = yes refl
...                                  | no  j≢k  = no λ { refl → j≢k refl }

\end{code}
}
\begin{code}

funcEq : Decidable≡ Function
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

funcEq (func n j) (func m k) with natEq n m
...                          | no  n≢m  = no λ { refl → n≢m refl }
...                          | yes refl with natEq j k
...                                     | yes refl = yes refl
...                                     | no  j≢k  = no λ { refl → j≢k refl }

\end{code}
}
\begin{code}

vecEq : ∀{n} {A : Set} → Decidable≡ A → Decidable≡ (Vec A n)
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

vecEq eq [] [] = yes refl
vecEq eq (x ∷ xs) (y ∷ ys) with eq x y
...                        | no  x≢y  = no λ { refl → x≢y refl }
...                        | yes refl with vecEq eq xs ys
...                                   | yes refl  = yes refl
...                                   | no  xs≢xy = no λ { refl → xs≢xy refl }

\end{code}
}
\begin{code}

termEq : Decidable≡ Term
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

termEq (varterm x)     (varterm y)     with varEq x y
...                                    | yes refl = yes refl
...                                    | no  x≢y  = no λ { refl → x≢y refl }
termEq (varterm x)     (functerm f ts) = no λ ()
termEq (functerm f ts) (varterm x)     = no λ ()
termEq (functerm f []) (functerm g []) with funcEq f g
...                                    | yes refl = yes refl
...                                    | no  f≢g  = no λ { refl → f≢g refl }
termEq (functerm f []) (functerm g (_ ∷ _)) = no λ ()
termEq (functerm f (_ ∷ _)) (functerm g []) = no λ ()
termEq
  (functerm (func n (suc j)) (u ∷ us)) (functerm (func m (suc k)) (v ∷ vs))
  with natEq j k
... | no  j≢k  = no λ { refl → j≢k refl }
... | yes refl with termEq u v
...   | no  u≢v  = no λ { refl → u≢v refl }
...   | yes refl
        with termEq (functerm (func n j) us) (functerm (func m k) vs)
...     | yes refl = yes refl
...     | no  neq  = no λ { refl → neq refl }

\end{code}
}
\begin{code}

formulaEq : Decidable≡ Formula
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

formulaEq (atom r xs) (atom s ys)
    with natEq (relarity r) (relarity s)
... | no ar≢as = no λ { refl → ar≢as refl }
... | yes refl with (relEq r s) | (vecEq termEq xs ys)
...            | yes refl | yes refl  = yes refl
...            | _        | no  xs≢ys = no λ { refl → xs≢ys refl }
...            | no  r≢s  | _         = no λ { refl → r≢s refl }
formulaEq (α ⇒ β) (γ ⇒ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  β≢δ  = no λ { refl → β≢δ refl }
...                       | no  α≢γ  | _        = no λ { refl → α≢γ refl }
formulaEq (α ∧ β) (γ ∧ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  β≢δ  = no λ { refl → β≢δ refl }
...                       | no  α≢γ  | _        = no λ { refl → α≢γ refl }
formulaEq (α ∨ β) (γ ∨ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  β≢δ  = no λ { refl → β≢δ refl }
...                       | no  α≢γ  | _        = no λ { refl → α≢γ refl }
formulaEq (Λ x α) (Λ y β) with (varEq x y) | (formulaEq α β)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  α≢β  = no λ { refl → α≢β refl }
...                       | no  x≢y  | _        = no λ { refl → x≢y refl }
formulaEq (V x α) (V y β) with (varEq x y) | (formulaEq α β)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  α≢β  = no λ { refl → α≢β refl }
...                       | no  x≢y  | _        = no λ { refl → x≢y refl }
formulaEq (atom r us) (γ ⇒ δ)     = no λ ()
formulaEq (atom r us) (γ ∧ δ)     = no λ ()
formulaEq (atom r us) (γ ∨ δ)     = no λ ()
formulaEq (atom r us) (Λ y γ)     = no λ ()
formulaEq (atom r us) (V y γ)     = no λ ()
formulaEq (α ⇒ β)     (atom r vs) = no λ ()
formulaEq (α ⇒ β)     (γ ∧ δ)     = no λ ()
formulaEq (α ⇒ β)     (γ ∨ δ)     = no λ ()
formulaEq (α ⇒ β)     (Λ y γ)     = no λ ()
formulaEq (α ⇒ β)     (V y γ)     = no λ ()
formulaEq (α ∧ β)     (atom r vs) = no λ ()
formulaEq (α ∧ β)     (γ ⇒ δ)     = no λ ()
formulaEq (α ∧ β)     (γ ∨ δ)     = no λ ()
formulaEq (α ∧ β)     (Λ y γ)     = no λ ()
formulaEq (α ∧ β)     (V y γ)     = no λ ()
formulaEq (α ∨ β)     (atom r vs) = no λ ()
formulaEq (α ∨ β)     (γ ⇒ δ)     = no λ ()
formulaEq (α ∨ β)     (γ ∧ δ)     = no λ ()
formulaEq (α ∨ β)     (Λ y γ)     = no λ ()
formulaEq (α ∨ β)     (V y γ)     = no λ ()
formulaEq (Λ x α)     (atom r vs) = no λ ()
formulaEq (Λ x α)     (γ ⇒ δ)     = no λ ()
formulaEq (Λ x α)     (γ ∧ δ)     = no λ ()
formulaEq (Λ x α)     (γ ∨ δ)     = no λ ()
formulaEq (Λ x α)     (V y γ)     = no λ ()
formulaEq (V x α)     (atom r vs) = no λ ()
formulaEq (V x α)     (γ ⇒ δ)     = no λ ()
formulaEq (V x α)     (γ ∧ δ)     = no λ ()
formulaEq (V x α)     (γ ∨ δ)     = no λ ()
formulaEq (V x α)     (Λ y γ)     = no λ ()

\end{code}
}

\subsection{Variable freedom}

We define the conditions for a variable to be \emph{not free} in a formula.
Instead of first defining \emph{free} and then taking \emph{not free} to be the
negation, we use a positive definition for not free, since later definitions
only ever require proof that a variable is not free.

For a given term $t$, $x$ is not in $t$ if $t$ is a variable other than $x$.
Otherwise if the term is a function on arguments $ts$, then $x$ is not in $t$
if it is not anywhere in $ts$, which can be checked by applying \inline{All} to
this definition.  Separating the declaration and definition of
\inline{_NotInTerm_} allows it to be defined mutually with the case for a
vector of terms.
\begin{code}

data _NotInTerm_ (x : Variable) : Term → Set

_NotInTerms_ : ∀{n} → Variable → Vec Term n → Set
x NotInTerms ts = All (x NotInTerm_) ts

data _NotInTerm_ x where
  varterm  : ∀{y} → x ≢ y → x NotInTerm (varterm y)
  functerm : ∀{f} {us : Vec Term (funcarity f)}
                  → x NotInTerms us → x NotInTerm (functerm f us)

\end{code}

A variable is now shown to be not free in a formula with the obvious recursive
definition. It is not free inside an atom if it is not inside that atom,
meaning it is not in the terms that the relation is operating on. It is not
free inside a quantification over a subformula either if it is the
quantification variable, or else if it is not free in the subformula. Separate
constructors are given for each case.
\todo{Notation: \inline{Λ∣}?}
\begin{code}

data _NotFreeIn_ : Variable → Formula → Set where
  atom : ∀{x r} {ts : Vec Term (relarity r)}
                  → x NotInTerms ts → x NotFreeIn (atom r ts)
  _⇒_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ⇒ β)
  _∧_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ∧ β)
  _∨_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ∨ β)
  Λ∣   : ∀ x α    → x NotFreeIn Λ x α
  V∣   : ∀ x α    → x NotFreeIn V x α
  Λ    : ∀{x α}   → ∀ y → x NotFreeIn α → x NotFreeIn Λ y α
  V    : ∀{x α}   → ∀ y → x NotFreeIn α → x NotFreeIn V y α

\end{code}

We now prove that the above predicate is decidable.

\begin{lemma}[\inline{_notInTerms_}]
Variable occurrence within a vector of terms is decidable.
\end{lemma}
\begin{proof}
Search through the vector for occurrences of the variable. In the following
code we will use names like \inline{x∉t} to denote proofs of `$x$ is not in
term $t$, \inline{x∉ts} for `$x$ is not in any terms in $ts$', and \inline{x∉α}
for `$x$ is not free in $\alpha$`.
\begin{code}

_notInTerms_ : ∀{n} → ∀ x → (ts : Vec Term n) → Dec (x NotInTerms ts)
x notInTerms [] = yes []
\end{code}
To check against a variable term, use the decidable equality of variables, then
recurse over the rest of the terms.
\begin{code}
x notInTerms (varterm y ∷ ts) with varEq x y
...    | yes refl = no λ { (varterm x≢x ∷ _) → x≢x refl }
...    | no  x≢y  with x notInTerms ts
...               | yes x∉ts = yes (varterm x≢y ∷ x∉ts)
...               | no ¬x∉ts = no λ { (_ ∷ x∉ts) → ¬x∉ts x∉ts }
\end{code}
To check against a function term, recurse over the arguments, then recurse over
the rest of the terms.
\begin{code}
x notInTerms (functerm f us ∷ ts) with x notInTerms us
...    | no ¬x∉us = no λ { (functerm x∉us ∷ _) → ¬x∉us x∉us }
...    | yes x∉us with x notInTerms ts
...               | yes x∉ts = yes (functerm x∉us ∷ x∉ts)
...               | no ¬x∉ts = no λ { (_ ∷ x∉ts) → ¬x∉ts x∉ts }

\end{code}
Each case checks if $x$ is free in the remaining terms in the vector. A shorter
proof would do this check at the same time as doing a case split on the first
term. However, if a term for which $x$ is free is found, it is not necessary to
continue recursing through the vector, so it is better computationally not to
do so.
\end{proof}

The same logic can be used for a single term, calling the above function to
check function arguments. The proposition \inline{_NotInTerms_} is defined
using \inline{All} and \inline{_NotInTerm_}, so it is tempting to try to first
prove that the single term case is decidable, and then generalise to vectors
using the lemma that \inline{All} is decidable for decidable predicates.
However, this would not be structurally recursive, and so Agda would not see
this as terminating. Above, the case \mintinline{agda}{x notInTerms t ∷ ts}
depends on the result of \inline{x notInTerms ts}, which is in fact primitively
recursive. However, if it instead depended on the result of \inline{all (x
notInTerm_) ts}, Agda cannot determine that \inline{x notInTerm_} will be
applied only to arguments structurally smaller than \inline{t ∷ ts}.
\begin{code}

_notInTerm_ : (x : Variable) → (t : Term) → Dec (x NotInTerm t)
x notInTerm varterm y     with varEq x y
...                       | yes refl = no  λ { (varterm x≢x) → x≢x refl }
...                       | no  x≢y  = yes (varterm x≢y)
x notInTerm functerm f ts with x notInTerms ts
...                       | yes x∉ts = yes (functerm x∉ts)
...                       | no ¬x∉ts = no  λ { (functerm x∉ts) → ¬x∉ts x∉ts }

\end{code}

\begin{proposition}[\inline{_notFreeIn_}]
Variable freedom is decidable.
\end{proposition}
\begin{proof}
For atoms, apply the lemma above. Otherwise, check recursively, checking if the
variable matches the quantifying variable in the case of quantifiers.
\begin{code}

_notFreeIn_ : (x : Variable) → (α : Formula) → Dec (x NotFreeIn α)
x notFreeIn atom r ts with x notInTerms ts
...                   | yes x∉ts = yes (atom x∉ts)
...                   | no ¬x∉ts = no λ { (atom x∉ts) → ¬x∉ts x∉ts }
x notFreeIn (α ⇒ β)   with x notFreeIn α | x notFreeIn β
...                   | yes x∉α | yes x∉β = yes (x∉α ⇒ x∉β)
...                   | _       | no ¬x∉β = no λ { (x∉α ⇒ x∉β) → ¬x∉β x∉β }
...                   | no ¬x∉α | _       = no λ { (x∉α ⇒ x∉β) → ¬x∉α x∉α }
x notFreeIn (α ∧ β)   with x notFreeIn α | x notFreeIn β
...                   | yes x∉α | yes x∉β = yes (x∉α ∧ x∉β)
...                   | _       | no ¬x∉β = no λ { (x∉α ∧ x∉β) → ¬x∉β x∉β }
...                   | no ¬x∉α | _       = no λ { (x∉α ∧ x∉β) → ¬x∉α x∉α }
x notFreeIn (α ∨ β)   with x notFreeIn α | x notFreeIn β
...                   | yes x∉α | yes x∉β = yes (x∉α ∨ x∉β)
...                   | _       | no ¬x∉β = no λ { (x∉α ∨ x∉β) → ¬x∉β x∉β }
...                   | no ¬x∉α | _       = no λ { (x∉α ∨ x∉β) → ¬x∉α x∉α }
x notFreeIn Λ  y α    with varEq x y
...                   | yes refl = yes (Λ∣ x α)
...                   | no x≢y with x notFreeIn α
...                            | yes x∉α = yes (Λ y x∉α)
...                            | no ¬x∉α = no λ { (Λ∣ x α)  → x≢y refl
                                                ; (Λ y x∉α) → ¬x∉α x∉α }
x notFreeIn V  y α    with varEq x y
...                   | yes refl = yes (V∣ x α)
...                   | no x≢y with x notFreeIn α
...                            | yes x∉α = yes (V y x∉α)
...                            | no ¬x∉α = no λ { (V∣ x α)  → x≢y refl
                                                ; (V y x∉α) → ¬x∉α x∉α }

\end{code}
\codeqed
\end{proof}


\subsection{Substitutions}

We define what it means for a formula $\beta$ to be obtained from $\alpha$ by
replacing all free instances of a variable $x$ with term $t$. The definitions
have a similar structure to that of \inline{_NotFreeIn_} above. The more
general case of replacing terms with terms is not needed for natural deduction.

Inside a vector of terms, wherever $x$ occurs, it is replaced with $t$. Any
variable distinct from $x$ is left unchanged. For a function application, $x$
is replaced with $t$ inside all of the arguments.
\begin{code}

data [_][_/_]≡_ : ∀{n} → Vec Term n → Variable → Term → Vec Term n → Set

data ⟨_⟩[_/_]≡_ : Term → Variable → Term → Term → Set where
  varterm≡ : ∀{x t} → ⟨ varterm x ⟩[ x / t ]≡ t
  varterm≢ : ∀{x t y} → x ≢ y → ⟨ varterm y ⟩[ x / t ]≡ varterm y
  functerm : ∀{x t f us vs} → [ us ][ x  / t ]≡ vs
               → ⟨ functerm f us ⟩[ x / t ]≡ functerm f vs

data [_][_/_]≡_ where
  []  : ∀{x t} → [ [] ][ x / t ]≡ []
  _∷_ : ∀{x t u v n} {us vs : Vec Term n}
        → ⟨ u ⟩[ x / t ]≡ v → [ us ][ x / t ]≡ vs
        → [ u ∷ us ][ x / t ]≡ (v ∷ vs)

\end{code}

The definition for formulae follows.
\begin{code}

data _[_/_]≡_ : Formula → Variable → Term → Formula → Set where
\end{code}
The \inline{ident} constructor gives the case that replacing $x$ with $x$
yields the original formula. While this can be proved as a derived rule, in
practice it is the case we usually want to use. Providing a constructor allows
Agda's proof search to apply this case easily.
\begin{code}
  ident : ∀ α x → α [ x / varterm x ]≡ α
\end{code}
If $x$ is not free in $\alpha$, then replacing it with any term should leave
$\alpha$ unchanged. This rule is not derivable when $t$ is not otherwise able
to be substituted for $x$ in $\alpha$. For example, without this constructor it
would not be possible to prove that $(\forall y A)[x/y]\equiv (\forall y A)$,
where $A$ is a propositional formula.
\begin{code}
  notfree : ∀{α x t} → x NotFreeIn α → α [ x / t ]≡ α
\end{code}
The propositional cases are similar to those of the \inline{_NotFreeIn_} type
above.
\begin{code}
  atom    : ∀{x t}
              → (r : Relation) → {xs ys : Vec Term (relarity r)}
              → [ xs ][ x / t ]≡ ys → (atom r xs) [ x / t ]≡ (atom r ys)
  _⇒_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′
              → (α ⇒ β) [ x / t ]≡ (α′ ⇒ β′)
  _∧_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′
              → (α ∧ β) [ x / t ]≡ (α′ ∧ β′)
  _∨_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′
              → (α ∨ β) [ x / t ]≡ (α′ ∨ β′)
\end{code}
Variable substitution for a quantified formula has two cases, which are similar
to their counterparts in \inline{_NotFreeIn_}. If $x$ is the quantification
variable, then the formula is unchanged.
\begin{code}
  Λ∣      : ∀{t} → ∀ x α → (Λ x α) [ x / t ]≡ (Λ x α)
  V∣      : ∀{t} → ∀ x α → (V x α) [ x / t ]≡ (V x α)
\end{code}
Finally, if $x$ is not the quantification variable, and the quantification
variable does not appear in $t$, then the substitution simply occurs inside the
quantification.
\begin{code}
  Λ       : ∀{α β x y t} → x ≢ y → y NotInTerm t
              → α [ x / t ]≡ β → (Λ y α) [ x / t ]≡ (Λ y β)
  V       : ∀{α β x y t} → x ≢ y → y NotInTerm t
              → α [ x / t ]≡ β → (V y α) [ x / t ]≡ (V y β)

\end{code}

Given $\alpha$, $x$, $t$, the $\beta$ satisfying $\alpha[x/t]\equiv \beta$
should be unique, so that variable substitution is functional. This can first
be shown for the special cases \inline{ident} and \inline{notfree}, by
recursing through the constructors down to the atomic case, and recursing
through the term substitutions down to the variable terms. The proofs simply
have \inline{refl} on the right side of every line, and are omitted. Their
structures are very similar to the two proofs that follow afterward.
\begin{code}

subIdentFunc : ∀{α x β} → α [ x / varterm x ]≡ β → α ≡ β
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

subIdentFunc (ident α x) = refl
subIdentFunc (notfree x) = refl
subIdentFunc (atom r ts) = vecEq→Eq (termsLemma ts)
  where
    vecEq→Eq : {us vs : Vec Term (relarity r)}
               → us ≡ vs → atom r us ≡ atom r vs
    vecEq→Eq refl = refl
    termsLemma : ∀{n x} {us vs : Vec Term n}
                   → [ us ][ x / varterm x ]≡ vs → us ≡ vs
    termsLemma []                  = refl
    termsLemma (r            ∷ rs) with termsLemma rs
    termsLemma (varterm≡     ∷ rs) | refl = refl
    termsLemma (varterm≢ x≢y ∷ rs) | refl = refl
    termsLemma (functerm ts  ∷ rs) | refl rewrite termsLemma ts = refl
subIdentFunc (subα ⇒ subβ) with subIdentFunc subα | subIdentFunc subβ
...                   | refl | refl = refl
subIdentFunc (subα ∧ subβ) with subIdentFunc subα | subIdentFunc subβ
...                   | refl | refl = refl
subIdentFunc (subα ∨ subβ) with subIdentFunc subα | subIdentFunc subβ
...                   | refl | refl = refl
subIdentFunc (Λ∣ x α) = refl
subIdentFunc (V∣ x α) = refl
subIdentFunc (Λ x≢y y∉x sub) rewrite subIdentFunc sub = refl
subIdentFunc (V x≢y y∉x sub) rewrite subIdentFunc sub = refl

\end{code}
}
\begin{code}
subNotFreeFunc : ∀{α x t β} → α [ x / t ]≡ β → x NotFreeIn α → α ≡ β
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

subNotFreeFunc (ident α x) x∉α = refl
subNotFreeFunc (notfree x) x∉α = refl
subNotFreeFunc (atom p r) (atom x∉xs) = vecEq→Eq (termsLemma r x∉xs)
  where
    vecEq→Eq : {us vs : Vec Term (relarity p)}
               → us ≡ vs → atom p us ≡ atom p vs
    vecEq→Eq refl = refl
    termsLemma : ∀{n x t} {us vs : Vec Term n}
                  → [ us ][ x / t ]≡ vs → x NotInTerms us → us ≡ vs
    termsLemma [] x∉us = refl
    termsLemma (r ∷ rs) (x∉u ∷ x∉us) with termsLemma rs x∉us
    termsLemma (varterm≡     ∷ rs) (varterm x≢x   ∷ x∉us) | refl = ⊥-elim (x≢x refl)
    termsLemma (varterm≢ x≢y ∷ rs) (x∉u           ∷ x∉us) | refl = refl
    termsLemma (functerm rt  ∷ rs) (functerm x∉ts ∷ x∉us) | refl
               rewrite termsLemma rt x∉ts = refl
subNotFreeFunc (subα ⇒ subβ) (x∉α ⇒ x∉β) with subNotFreeFunc subα x∉α | subNotFreeFunc subβ x∉β
...                                 | refl | refl = refl
subNotFreeFunc (subα ∧ subβ) (x∉α ∧ x∉β) with subNotFreeFunc subα x∉α | subNotFreeFunc subβ x∉β
...                                 | refl | refl = refl
subNotFreeFunc (subα ∨ subβ) (x∉α ∨ x∉β) with subNotFreeFunc subα x∉α | subNotFreeFunc subβ x∉β
...                                 | refl | refl = refl
subNotFreeFunc (Λ∣ x α) _ = refl
subNotFreeFunc (V∣ x α) _ = refl
subNotFreeFunc (Λ x≢x _ r) (Λ∣ x α) = ⊥-elim (x≢x refl)
subNotFreeFunc (Λ x≢y _ r) (Λ y x∉α) rewrite subNotFreeFunc r x∉α = refl
subNotFreeFunc (V x≢y _ r) (V∣ x α) = ⊥-elim (x≢y refl)
subNotFreeFunc (V x≢y _ r) (V y x∉α) rewrite subNotFreeFunc r x∉α = refl

\end{code}
}

\begin{lemma}[\inline{subTermsFunc}]
Variable substitution inside a vector of terms is functional.
\end{lemma}
\begin{proof}
The constructors for term substitution have no overlap.
\begin{code}

subTermsFunc : ∀{n x t} {us vs ws : Vec Term n}
               → [ us ][ x / t ]≡ vs → [ us ][ x / t ]≡ ws → vs ≡ ws
subTermsFunc [] [] = refl
\end{code}
First recurse over the rest of the two vectors.
\begin{code}
subTermsFunc (s ∷ ss) (r ∷ rs) with subTermsFunc ss rs
\end{code}
It is possible to pattern match inside the \inline{with} block to examine the
two substitutions made for the heads of the vectors. In the case that the first
term is substituted using \inline{varterm≡} in each case, the resulting vectors
must both have $x$ at the head, so the proof is \inline{refl}.
\begin{code}
subTermsFunc (varterm≡     ∷ _) (varterm≡     ∷ _) | refl = refl
\end{code}
It would be contradictory for the first term in $us$ to both match and differ
from $x$.
\begin{code}
subTermsFunc (varterm≡     ∷ _) (varterm≢ x≢x ∷ _) | refl = ⊥-elim (x≢x refl)
subTermsFunc (varterm≢ x≢x ∷ _) (varterm≡     ∷ _) | refl = ⊥-elim (x≢x refl)
\end{code}
If the head of $us$ is a variable different from $x$, then it is unchanged in
each case, so the proof is \inline{refl}.
\begin{code}
subTermsFunc (varterm≢ x≢y ∷ _) (varterm≢ _   ∷ _) | refl = refl
\end{code}
Finally, in the case of a function, recurse over the vector of arguments.
The \inline{rewrite} construction uses a proof of equality to unify terms. It
is an abbreviation for doing \inline{with}-abstraction on a proof of
\inline{refl}.
\begin{code}
subTermsFunc (functerm st  ∷ _) (functerm rt  ∷ _)
             | refl rewrite subTermsFunc st rt = refl

\end{code}
\codeqed
\end{proof}

\begin{proposition}[\inline{subFunc}]
Variable substitution is functional.
\end{proposition}
\begin{proof}
$ $
\begin{code}

subFunc : ∀{x t α β γ} → α [ x / t ]≡ β → α [ x / t ]≡ γ → β ≡ γ
\end{code}
If either substitution came from \inline{ident} or \inline{notfree}, invoke one
of the above lemmas. If they occurred in the right substitution, the lemmas
prove $\gamma \equiv \beta$, so \inline{rewrite} is used to recover $\beta
\equiv \gamma$.
\begin{code}
subFunc (ident α x)   r             = subIdentFunc r
subFunc (notfree x∉α) r             = subNotFreeFunc r x∉α
subFunc r             (ident α x)   rewrite subIdentFunc r       = refl
subFunc r             (notfree x∉α) rewrite subNotFreeFunc r x∉α = refl
\end{code}
The atomic case comes from the previous lemma.
\begin{code}
subFunc (atom p s)    (atom .p r)   rewrite subTermsFunc s r = refl
\end{code}
The propositional connectives can be proved inductively.
\begin{code}
subFunc (s₁ ⇒ s₂)     (r₁ ⇒ r₂)     with subFunc s₁ r₁ | subFunc s₂ r₂
...                                 | refl | refl = refl
subFunc (s₁ ∧ s₂)     (r₁ ∧ r₂)     with subFunc s₁ r₁ | subFunc s₂ r₂
...                                 | refl | refl = refl
subFunc (s₁ ∨ s₂)     (r₁ ∨ r₂)     with subFunc s₁ r₁ | subFunc s₂ r₂
...                                 | refl | refl = refl
\end{code}
If the formula is a quantification over $x$, then neither substitution changes
the formula.
\begin{code}
subFunc (Λ∣ x α)      (Λ∣ .x .α)    = refl
subFunc (V∣ x α)      (V∣ .x .α)    = refl
\end{code}
It is contradictory for one substitution to occur by matching $x$
with the quantifier variable, and the other to have a different quantifier.
\begin{code}
subFunc (Λ∣ x α)      (Λ x≢x _ r)   = ⊥-elim (x≢x refl)
subFunc (V∣ x α)      (V x≢x _ r)   = ⊥-elim (x≢x refl)
subFunc (Λ x≢x _ s)   (Λ∣ x α)      = ⊥-elim (x≢x refl)
subFunc (V x≢x _ s)   (V∣ x α)      = ⊥-elim (x≢x refl)
\end{code}
Finally, if the formula is a quantification over a variable other than $x$,
then substitution occurs inside the quantified formula, so recurse inside those
substitutions.
\begin{code}
subFunc (Λ _ _ s)     (Λ _ _ r)     rewrite subFunc s r = refl
subFunc (V _ _ s)     (V _ _ r)     rewrite subFunc s r = refl

\end{code}
\codeqed
\end{proof}

We have now shown that substitution is functional, and so would like to
construct a function that computes substitutions. However, substitutions do not
always exist. For example, there is no way of constructing a formula for
$(\forall y P x)[x/y]$. In general, $\alpha [x/t]$ exists only if $t$ is
\emph{free for} $x$ \emph{in} $\alpha$, meaning no variables in $t$ would
become bound inside $\alpha$. This can be formalised by using (with minor
modification) the rules of \cite{vandalen}.
\begin{code}

data _FreeFor_In_ (t : Term) (x : Variable) : Formula → Set where
  notfree : ∀{α} → x NotFreeIn α → t FreeFor x In α
  atom    : ∀ r us → t FreeFor x In atom r us
  _⇒_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β
                     → t FreeFor x In α ⇒ β
  _∧_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β
                     → t FreeFor x In α ∧ β
  _∨_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β
                     → t FreeFor x In α ∨ β
  Λ∣      : ∀ α → t FreeFor x In Λ x α
  V∣      : ∀ α → t FreeFor x In V x α
  Λ       : ∀{α y} → y NotInTerm t → t FreeFor x In α → t FreeFor x In Λ y α
  V       : ∀{α y} → y NotInTerm t → t FreeFor x In α → t FreeFor x In V y α

\end{code}

The definitions above for variable substitution lead directly to a procedure
for computing substitutions. Given $\alpha$, $x$, $t$, and a proof that $t$ is
free for $x$ in $\alpha$, we compute a $\beta$ and a proof that
$\alpha[x/t] \equiv \beta$.

The built-in sigma (dependent sum) type has been imported. A simplified version
of its definition is commented below.
\begin{code}

{-
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst
-}

\end{code}
\inline{Σ A B} can be proved by providing an $x$ of type $A$, and a proof of $B
x$, so that it encapsulates both a value and a proof regarding that value.
This means sigma type can be used to define existential propositions.

\begin{lemma}
Every vector of terms has a substitution of any variable with any term.
\end{lemma}
\begin{proof}
Recurse through all function arguments, and replace any variables equal to $x$
with $t$. We do a case split on the first term, and use a \inline{with} block
to get the substitution for the rest of the vector simultaneously, since this
substitution is required in either case.
\begin{code}

[_][_/_] : ∀{n} → (us : Vec Term n) → ∀ x t → Σ _ [ us ][ x / t ]≡_
[ []                 ][ x / t ] = [] , []
[ u             ∷ us ][ x / t ] with [ us ][ x / t ]
[ varterm y     ∷ us ][ x / t ] | vs , vspf with varEq x y
...    | yes refl = (t ∷ vs) , (varterm≡ ∷ vspf)
...    | no  x≢y  = (varterm y ∷ vs) , (varterm≢ x≢y ∷ vspf)
[ functerm f ws ∷ us ][ x / t ] | vs , vspf with [ ws ][ x / t ]
...    | xs , xspf = (functerm f xs ∷ vs) , (functerm xspf ∷ vspf)

\end{code}
\codeqed
\end{proof}

\begin{proposition}
If $t$ is free for $x$ in $\alpha$, then there is a substitution of $x$ with
$t$ in $\alpha$.
\end{proposition}
\begin{proof}
The proof that $t$ is free for $x$ in formula must be supplied.  The term $t$
is fixed by supplying such a proof, so for convenience of notation, the proof
is supplied in place of the term.
\begin{code}

_[_/_] : ∀{t} → ∀ α x → t FreeFor x In α → Σ Formula (α [ x / t ]≡_)
α [ x / notfree ¬x∉α ]       = α , notfree ¬x∉α
\end{code}
For atomic formulae, apply the above lemma.
\begin{code}
_[_/_] {t} (atom r ts) x tff with [ ts ][ x / t ]
...                          | ts′ , tspf = atom r ts′ , atom r tspf
\end{code}
For the propositional connectives, the substitution is obtained recursively.
\begin{code}
(α ⇒ β) [ x / tffα ⇒ tffβ ]  with α [ x / tffα ] | β [ x / tffβ ]
...                          | α′ , αpf | β′ , βpf = α′ ⇒ β′ , αpf ⇒ βpf
(α ∧ β) [ x / tffα ∧ tffβ ]  with α [ x / tffα ] | β [ x / tffβ ]
...                          | α′ , αpf | β′ , βpf = α′ ∧ β′ , αpf ∧ βpf
(α ∨ β) [ x / tffα ∨ tffβ ]  with α [ x / tffα ] | β [ x / tffβ ]
...                          | α′ , αpf | β′ , βpf = α′ ∨ β′ , αpf ∨ βpf
\end{code}
For generalisation, check if $x$ is the quantifier variable, and if so do
nothing.  Otherwise, recurse.
\begin{code}
Λ y α [ .y / Λ∣ .α ]         = Λ y α , Λ∣ y α
Λ y α [ x / Λ y∉t tffα ]     with varEq x y
...                          | yes refl = Λ y α , Λ∣ y α
...                          | no  x≢y  with α [ x / tffα ]
...                                     | α′ , αpf = Λ y α′ , Λ x≢y y∉t αpf
V y α [ .y / V∣ .α ]         = V y α , V∣ y α
V y α [ x / V y∉t tffα ]     with varEq x y
...                          | yes refl = V y α , V∣ y α
...                          | no  x≢y  with α [ x / tffα ]
...                                     | α′ , αpf = V y α′ , V x≢y y∉t αpf

\end{code}
\codeqed
\end{proof}

We have proved that if $t$ is free for $x$ in $α$ then $α[x/t]$ exists. The
converse is also true, meaning that \inline{_FreeFor_In_} precisely captures
the notion of a substitution being possible. The proof is straightforward by
induction on formula substitution, with the base case of atomic formulae being
trivial.
\begin{code}

subFreeFor : ∀{α x t β} → α [ x / t ]≡ β → t FreeFor x In α
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

subFreeFor (ident (atom r ts) x) = atom r ts
subFreeFor (ident (α ⇒ β) x) = subFreeFor (ident α x) ⇒ subFreeFor (ident β x)
subFreeFor (ident (α ∧ β) x) = subFreeFor (ident α x) ∧ subFreeFor (ident β x)
subFreeFor (ident (α ∨ β) x) = subFreeFor (ident α x) ∨ subFreeFor (ident β x)
subFreeFor (ident (Λ y α) x) with varEq y x
...                          | yes refl = Λ∣ α
...                          | no  y≢x  = Λ (varterm y≢x) (subFreeFor (ident α x))
subFreeFor (ident (V y α) x) with varEq y x
...                          | yes refl = V∣ α
...                          | no  y≢x  = V (varterm y≢x) (subFreeFor (ident α x))
subFreeFor (notfree x) = notfree x
subFreeFor (atom r subts) = atom r _
subFreeFor (subα ⇒ subβ) = subFreeFor subα ⇒ subFreeFor subβ
subFreeFor (subα ∧ subβ) = subFreeFor subα ∧ subFreeFor subβ
subFreeFor (subα ∨ subβ) = subFreeFor subα ∨ subFreeFor subβ
subFreeFor (Λ∣ x α) = Λ∣ α
subFreeFor (V∣ x α) = V∣ α
subFreeFor (Λ x≢y y∉t sub) = Λ y∉t (subFreeFor sub)
subFreeFor (V x≢y y∉t sub) = V y∉t (subFreeFor sub)

\end{code}
}

\begin{proposition}
If a variable has been substituted by a term not involving that variable, then
the variable is not free in the resulting formula.
\end{proposition}
\begin{proof}
$ $
\begin{code}

subNotFree : ∀{α x t β} → x NotInTerm t → α [ x / t ]≡ β → x NotFreeIn β
\end{code}
The case where the substitution was constructed by \inline{ident} is absurd,
since $x$ can't not be in term $x$.
\begin{code}
subNotFree (varterm x≢x) (ident α x)   = ⊥-elim (x≢x refl)
\end{code}
If the substitution was constructed by \inline{notfree}, then $\alpha \equiv
\beta$, so $x$ is not free in $\beta$.
\begin{code}
subNotFree x∉t           (notfree x∉α) = x∉α
\end{code}
For atomic formulae, we use an inline lemma that the proposition holds for
vectors of terms. Every variable in a term is either equal to $x$, and so gets
replaced with $t$, or else differs from $x$.
\begin{code}
subNotFree x∉t (atom r subus)  = atom (φ x∉t subus)
  where
    φ : ∀{n x t} {us vs : Vec Term n} → x NotInTerm t
                      → [ us ][ x / t ]≡ vs → x NotInTerms vs
    φ x∉t []                  = []
    φ x∉t (varterm≡     ∷ subus) = x∉t                  ∷ φ x∉t subus
    φ x∉t (varterm≢ neq ∷ subus) = varterm neq          ∷ φ x∉t subus
    φ x∉t (functerm sub ∷ subus) = functerm (φ x∉t sub) ∷ φ x∉t subus
\end{code}
The remaining cases follow by recursion.
\begin{code}
subNotFree x∉t (subα ⇒ subβ)   = subNotFree x∉t subα ⇒ subNotFree x∉t subβ
subNotFree x∉t (subα ∧ subβ)   = subNotFree x∉t subα ∧ subNotFree x∉t subβ
subNotFree x∉t (subα ∨ subβ)   = subNotFree x∉t subα ∨ subNotFree x∉t subβ
subNotFree x∉t (Λ∣ y α)        = Λ∣ y α
subNotFree x∉t (Λ x≢y y∉t sub) = Λ _ (subNotFree x∉t sub)
subNotFree x∉t (V∣ y α)        = V∣ y α
subNotFree x∉t (V x≢y y∉t sub) = V _ (subNotFree x∉t sub)

\end{code}
\codeqed
\end{proof}


\todo{Explain and neaten}
\begin{code}

subInverse : ∀{ω α x β} → ω NotFreeIn α
                          → α [ x / varterm ω ]≡ β → β [ ω / varterm x ]≡ α
subInverse _           (ident α x)    = ident α x
subInverse ω∉α         (notfree x∉α)  = notfree ω∉α
subInverse (atom x∉ts) (atom r subts) = atom r (termsLemma x∉ts subts)
  where
    termsLemma : ∀{n x ω} {us vs : Vec Term n} → ω NotInTerms us
                 → [ us ][ x / varterm ω ]≡ vs → [ vs ][ ω / varterm x ]≡ us
    termsLemma ω∉us [] = []
    termsLemma (_ ∷ ω∉us) (varterm≡ ∷ subus) = varterm≡ ∷ termsLemma ω∉us subus
    termsLemma (varterm ω≢y ∷ ω∉us) (varterm≢ x≢ω ∷ subus) = varterm≢ ω≢y ∷ termsLemma ω∉us subus
    termsLemma (functerm ω∉ts ∷ ω∉us) (functerm subts ∷ subus) = functerm (termsLemma ω∉ts subts) ∷ termsLemma ω∉us subus
subInverse (ω∉α ⇒ ω∉β) (subα ⇒ subβ) = subInverse ω∉α subα ⇒ subInverse ω∉β subβ
subInverse (ω∉α ∧ ω∉β) (subα ∧ subβ) = subInverse ω∉α subα ∧ subInverse ω∉β subβ
subInverse (ω∉α ∨ ω∉β) (subα ∨ subβ) = subInverse ω∉α subα ∨ subInverse ω∉β subβ
subInverse ω∉α          (Λ∣ x α)              = notfree ω∉α
subInverse (Λ∣ x α)      (Λ _ (varterm x≢x) _) = ⊥-elim (x≢x refl)
subInverse ω∉α          (V∣ x α)              = notfree ω∉α
subInverse (V∣ x α)      (V _ (varterm x≢x) _) = ⊥-elim (x≢x refl)
subInverse {ω} (Λ y ω∉α) (Λ x≢y y∉ω subα)           with varEq ω y
subInverse {ω} (Λ y ω∉α) (Λ x≢y y∉ω subα)           | no ω≢y = Λ ω≢y (varterm λ { refl → x≢y refl }) (subInverse ω∉α subα)
subInverse {.y} (Λ y ω∉α) (Λ x≢y (varterm y≢y) subα) | yes refl = ⊥-elim (y≢y refl)
subInverse {ω} (V y ω∉α) (V x≢y y∉ω subα)           with varEq ω y
subInverse {.y} (V y ω∉α) (V x≢y (varterm y≢y) subα) | yes refl = ⊥-elim (y≢y refl)
subInverse {ω} (V y ω∉α) (V x≢y y∉ω subα)           | no ω≢y = V ω≢y (varterm λ { refl → x≢y refl }) (subInverse ω∉α subα)


\end{code}

\subsection{Fresh variables}

A variable is \emph{fresh} if appears nowhere (free or bound) in a formula.
\begin{code}

data _FreshIn_ (x : Variable) : Formula → Set where
  atom : ∀{r ts} → x NotInTerms ts  → x FreshIn (atom r ts)
  _⇒_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ⇒ β
  _∧_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ∧ β
  _∨_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ∨ β
  Λ    : ∀{α y} → y ≢ x → x FreshIn α → x FreshIn Λ y α
  V    : ∀{α y} → y ≢ x → x FreshIn α → x FreshIn V y α

\end{code}

Certainly, if a variable is fresh in a formula, then it is also not free, and
every term is free for that variable. The proofs are trivial, and are omitted.
\begin{code}

freshNotFree : ∀{α x} → x FreshIn α → x NotFreeIn α
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

freshNotFree (atom x∉ts)   = atom x∉ts
freshNotFree (xfrα ⇒ xfrβ) = freshNotFree xfrα ⇒ freshNotFree xfrβ
freshNotFree (xfrα ∧ xfrβ) = freshNotFree xfrα ∧ freshNotFree xfrβ
freshNotFree (xfrα ∨ xfrβ) = freshNotFree xfrα ∨ freshNotFree xfrβ
freshNotFree (Λ _ xfrα)    = Λ _ (freshNotFree xfrα)
freshNotFree (V _ xfrα)    = V _ (freshNotFree xfrα)

\end{code}
}
\begin{code}

freshFreeFor : ∀{α x} → x FreshIn α → ∀ y → (varterm x) FreeFor y In α
-- Proof omitted.

\end{code}
\AgdaHide{
\begin{code}

freshFreeFor (atom _)      y = atom _ _
freshFreeFor (xfrα ⇒ xfrβ) y = freshFreeFor xfrα y ⇒ freshFreeFor xfrβ y
freshFreeFor (xfrα ∧ xfrβ) y = freshFreeFor xfrα y ∧ freshFreeFor xfrβ y
freshFreeFor (xfrα ∨ xfrβ) y = freshFreeFor xfrα y ∨ freshFreeFor xfrβ y
freshFreeFor (Λ x≢y xfrα)  y = Λ (varterm x≢y) (freshFreeFor xfrα y)
freshFreeFor (V x≢y xfrα)  y = V (varterm x≢y) (freshFreeFor xfrα y)

\end{code}
}

For the purposes of variable substitution, we will later need a way to generate
a fresh variable for a given formula. Only finitely many variables occur in a
given term or formula, so there is a greatest (with respect to the natural
number indexing) variable occurring in each term or formula; all variables
greater than this are fresh. We will first compute this variable, and then use
its successor. This means that the least fresh variable will not be found. For
example, for $P x_0 \lor P x_2$, we find that $x_3, x_4, \dotsc$ are fresh,
missing $x_1$. However, finding the least fresh variable cannot be done with a
simple recursive procedure. Consider $\alpha = (P x_0 \lor P x_2) \land P x_1$;
we find $x_1$ is fresh to the left of the conjunctive, and $x_0$ is fresh to
the right, but this does not indicate that $x_2$ will not be fresh in $\alpha$.

\begin{lemma}
There is an upper bound on the variables occurring in a given vector of terms.
\end{lemma}
\begin{proof}
We call this function \inline{maxVarTerms}, but wil not actually prove that
this is the least upper bound in particular. \todo{Upper bound?}
\begin{code}

maxVarTerms : ∀{k} → (ts : Vec Term k)
              → Σ Variable (λ ⌈ts⌉
                            → ∀ n → varidx ⌈ts⌉ < n → var n NotInTerms ts)
maxVarTerms []                   = var zero , (λ _ _ → [])
\end{code}
If the first term is a variable, check if its index is greater than or equal to
the greatest variable in the rest of the terms.
\begin{code}
maxVarTerms (varterm x     ∷ ts) with maxVarTerms ts
... | ⌈ts⌉ , tspf with compare (varidx x) (varidx ⌈ts⌉)
...               | more ⌈ts⌉≤x = x , maxIsx
  where
    maxIsx : ∀ n → (varidx x) < n → (var n) NotInTerms (varterm x ∷ ts)
    maxIsx n x<n = varterm (λ { refl → ℕdisorder x<n ≤refl })
                   ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤x) x<n)
\end{code}
Otherwise, use the greatest variable in the rest of the terms.
\begin{code}
...               | less x≤⌈ts⌉ = ⌈ts⌉ , ⌈ts⌉pf
  where
    ⌈ts⌉pf : ∀ n → varidx ⌈ts⌉ < n → var n NotInTerms (varterm x ∷ ts)
    ⌈ts⌉pf n ⌈ts⌉<n = varterm (λ { refl → ℕdisorder ⌈ts⌉<n x≤⌈ts⌉ })
                      ∷ tspf n ⌈ts⌉<n
\end{code}
If the first term is a function, then check if the greatest variable in its
arguments is greater than or equal to the greatest variable of the rest of the
terms.
\begin{code}
maxVarTerms (functerm f us ∷ ts) with maxVarTerms us | maxVarTerms ts
... | ⌈us⌉ , uspf | ⌈ts⌉ , tspf with compare (varidx ⌈us⌉) (varidx ⌈ts⌉)
...                             | more ⌈ts⌉≤⌈us⌉ = ⌈us⌉ , ⌈us⌉pf
  where
    ⌈us⌉pf : ∀ n → varidx ⌈us⌉ < n → (var n) NotInTerms (functerm f us ∷ ts)
    ⌈us⌉pf n ⌈us⌉<n = functerm (uspf n ⌈us⌉<n)
                      ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤⌈us⌉) ⌈us⌉<n)
\end{code}
If not, use the greatest variable in the rest of the terms.
\begin{code}
...                             | less ⌈us⌉≤⌈ts⌉ = ⌈ts⌉ , ⌈ts⌉pf
  where
    ⌈ts⌉pf : ∀ n → varidx ⌈ts⌉ < n → (var n) NotInTerms (functerm f us ∷ ts)
    ⌈ts⌉pf n ⌈ts⌉<n = functerm (uspf n (≤trans (sn≤sm ⌈us⌉≤⌈ts⌉) ⌈ts⌉<n))
                      ∷ tspf n ⌈ts⌉<n

\end{code}
\codeqed
\end{proof}


\begin{proposition}
There is an upper bound on the variables occurring in a given formula.
\end{proposition}
\begin{proof}
$ $
\begin{code}
maxVar : ∀ α → Σ Variable λ ⌈α⌉ → ∀ n → varidx ⌈α⌉ < n → var n FreshIn α
\end{code}
In the atomic case, apply the above lemma to find the greatest variable
occuring.
\begin{code}
maxVar (atom r ts) with maxVarTerms ts
...                  | ⌈ts⌉ , tspf = ⌈ts⌉ , λ n ⌈ts⌉<n → atom (tspf n ⌈ts⌉<n)
\end{code}
If all variables greater than $\lceil\alpha\rceil$ are fresh in $\alpha$, and
all greater than $\lceil\beta\rceil$ are fresh in $\beta$, then any variable
greater than $\max\{\lceil\alpha\rceil, \lceil\beta\rceil\}$ will be fresh in
$\alpha \rightarrow \beta$.
\begin{code}
maxVar (α ⇒ β) with maxVar α | maxVar β
...    | ⌈α⌉ , αpf | ⌈β⌉ , βpf with compare (varidx ⌈α⌉) (varidx ⌈β⌉)
...                            | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , maxIs⌈β⌉
    where
      maxIs⌈β⌉ : ∀ n → varidx ⌈β⌉ < n → var n FreshIn (α ⇒ β)
      maxIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ⇒ βpf n ⌈β⌉<n
...                            | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
    where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn (α ⇒ β)
      maxIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ⇒ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
\end{code}
The same reasoning applies to conjunction
\begin{code}
maxVar (α ∧ β) with maxVar α | maxVar β
...    | ⌈α⌉ , αpf | ⌈β⌉ , βpf with compare (varidx ⌈α⌉) (varidx ⌈β⌉)
...                            | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , maxIs⌈β⌉
    where
      maxIs⌈β⌉ : ∀ n → varidx ⌈β⌉ < n → var n FreshIn (α ∧ β)
      maxIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∧ βpf n ⌈β⌉<n
...                            | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
    where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn (α ∧ β)
      maxIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∧ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
\end{code}
and disjunction.
\begin{code}
maxVar (α ∨ β) with maxVar α | maxVar β
...    | ⌈α⌉ , αpf | ⌈β⌉ , βpf with compare (varidx ⌈α⌉) (varidx ⌈β⌉)
...                            | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , maxIs⌈β⌉
    where
      maxIs⌈β⌉ : ∀ n → varidx ⌈β⌉ < n → var n FreshIn (α ∨ β)
      maxIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∨ βpf n ⌈β⌉<n
...                            | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
    where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn (α ∨ β)
      maxIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∨ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
\end{code}
For a universal generalisation $\forall x \alpha$, take the greater of
$\lceil\alpha\rceil$ and $x$.
\begin{code}
maxVar (Λ x α) with maxVar α
...              | ⌈α⌉ , αpf with compare (varidx x) (varidx ⌈α⌉)
...                          | less x≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
  where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn Λ x α
      maxIs⌈α⌉ n ⌈α⌉<n = Λ (λ { refl → ℕdisorder ⌈α⌉<n x≤⌈α⌉ }) (αpf n ⌈α⌉<n)
...                          | more ⌈α⌉≤x = x , maxIsx
  where
      maxIsx : ∀ n → varidx x < n → var n FreshIn Λ x α
      maxIsx n x<n = Λ (λ { refl → ℕdisorder x<n ≤refl })
                        (αpf n (≤trans (sn≤sm ⌈α⌉≤x) x<n))
\end{code}
The same applies for existential generalisation.
\begin{code}
maxVar (V x α) with maxVar α
...              | ⌈α⌉ , αpf with compare (varidx x) (varidx ⌈α⌉)
...                          | less x≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
  where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn V x α
      maxIs⌈α⌉ n ⌈α⌉<n = V (λ { refl → ℕdisorder ⌈α⌉<n x≤⌈α⌉ }) (αpf n ⌈α⌉<n)
...                          | more ⌈α⌉≤x = x , maxIsx
  where
      maxIsx : ∀ n → varidx x < n → var n FreshIn V x α
      maxIsx n x<n = V (λ { refl → ℕdisorder x<n ≤refl })
                        (αpf n (≤trans (sn≤sm ⌈α⌉≤x) x<n))

\end{code}
\codeqed
\end{proof}

Finally, a fresh variable can be extracted by choosing the successor of
the variable given by the proof above.
\begin{code}
fresh : ∀ α → Σ Variable (_FreshIn α)
fresh α with maxVar α
...     | ⌈α⌉ , αpf = var (suc (varidx ⌈α⌉)) , αpf (suc (varidx ⌈α⌉)) ≤refl

\end{code}
