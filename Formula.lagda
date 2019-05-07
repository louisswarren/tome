\begin{code}

module Formula where

open import Agda.Builtin.Sigma

open import Decidable
open import Nat
open import Vec

\end{code}

\subsection{Basic definitions}

We adopt the definitions of \citet{schwichtenberg}. In particular, there are
countably many variables, and there are countably many function symbols of each
(natural) airty. Function symbols of different arities with the same index are
considered different.
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
and more useful to index using strings, strings are not supported by Agda's
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

We now define atoms (prime formulae), and the logical connectives, using
$\bigwedge$ and $\bigvee$ in place of $\forall$ and $\exists$, since $\forall$
is reserved by Agda.
\todo{Rename $\Lambda$ and $V$}
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

infixr 105 _⇒_ _⇔_
infixr 106 _∨_
infixr 107 _∧_

\end{code}

Equality of formulae is decidable. Logically, this follows from the fact that
formulae are inductively defined. The proof is obtained by case analysis, using
lemata on the types used to construct formulae. As these proofs are
unremarkable, and follow the same pattern as the proof for decidable equality
of natural numbers above, they are omitted from the latex-typeset form of this
file.
\begin{code}

varEq : Decidable≡ Variable
-- Proof omitted

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
-- Proof omitted

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
-- Proof omitted

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
-- Proof omitted

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
-- Proof omitted

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
-- Proof omitted

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

\subsection{Variable freedom and substitution}

We define the conditions for a variable to be \emph{not free} in a formula.
Instead of first defining \emph{free} and then taking \emph{not free} to be the
negation, we use a positive definition, since later definitions only ever
require proof that a variable is not free. For a given term $t$, $x$ is not
free in $t$ if $t$ is a variable other than $x$. Otherwise if the term is a
function on arguments $ts$, then $x$ is not free if it is not free anywhere in
$ts$, which can be checked by applying \inline{All} to this definition.
Separating the declaration and definition of \inline{_NotFreeInTerm_} allows it
to be defined mutually with the case for a vector of terms.
\begin{code}

data _NotFreeInTerm_ (x : Variable) : Term → Set

_NotFreeInTerms_ : ∀{n} → Variable → Vec Term n → Set
x NotFreeInTerms ts = All (x NotFreeInTerm_) ts

data _NotFreeInTerm_ x where
  varterm  : ∀{y} → x ≢ y → x NotFreeInTerm (varterm y)
  functerm : ∀{f} {us : Vec Term (funcarity f)}
               → x NotFreeInTerms us → x NotFreeInTerm (functerm f us)

\end{code}

A variable is shown to be not free in a formula with the obvious recursive
definition. It is not free inside a quantification over a subformula $\alpha$
either if it is the quantification variable, or else if it is not free in
$\alpha$.  Separate constructors are given for these. A variable is not free
inside an atom if it is not free within that atom, meaning it is not free in
the terms that the relation is operating on.
\todo{Notation: \inline{Λ∣}?}
\begin{code}

data _NotFreeIn_ : Variable → Formula → Set where
  atom : ∀{x r} {ts : Vec Term (relarity r)}
                  → x NotFreeInTerms ts → x NotFreeIn (atom r ts)
  _⇒_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ⇒ β)
  _∧_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ∧ β)
  _∨_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ∨ β)
  Λ∣   : ∀ x α    → x NotFreeIn Λ x α
  V∣   : ∀ x α    → x NotFreeIn V x α
  Λ    : ∀{x α}   → ∀ y → x NotFreeIn α → x NotFreeIn Λ y α
  V    : ∀{x α}   → ∀ y → x NotFreeIn α → x NotFreeIn V y α

\end{code}

We define what it means for a formula $\beta$ to be obtained from $\alpha$ by
replacing all instances of a variable $x$ with term $t$. It will later be shown
that such a $\beta$ is unique. The definitions have a similar structure to that
of \inline{_NotFreeIn_} above. Note that the more general case of replacing
terms with terms is not needed for natural deduction.

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
yields the original formula. While this is actually a derived rule, in practice
it is the case we usually want to use. Providing a constructor allows Agda's
proof search to solve this case easily.
\begin{code}
  ident : ∀ α x → α [ x / varterm x ]≡ α
\end{code}
If $x$ is in fact not free in $\alpha$, then replacing it with any term should
leave $\alpha$ unchanged. This rule is not derivable when $t$ is not free for
$x$ in $\alpha$. For example, without this constructor it would not be possible
to prove that $(\forall y A)[x/y]\equiv A$, where $A$ is a propositional
\todo{nullary predicate} formula.
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
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ⇒ β) [ x / t ]≡ (α′ ⇒ β′)
  _∧_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∧ β) [ x / t ]≡ (α′ ∧ β′)
  _∨_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∨ β) [ x / t ]≡ (α′ ∨ β′)
\end{code}
Variable substitution for a quantified formula has two cases, which are similar
to their counterparts in \inline{_NotFreeIn_}. If $x$ is the quantification
variable, then the formula is unchanged.
\begin{code}
  Λ∣      : ∀{t} → (x : Variable) → (α : Formula) → (Λ x α) [ x / t ]≡ (Λ x α)
  V∣      : ∀{t} → (x : Variable) → (α : Formula) → (V x α) [ x / t ]≡ (V x α)
\end{code}
If $x$ is not the quantification variable and $t$ is free for $x$ in in the
formula ($x$ is not free in term $t$), then the substitution simply occurs
inside the quantification.
\begin{code}
  Λ       : ∀{α β x y t} → x ≢ y → y NotFreeInTerm t
              → α [ x / t ]≡ β → (Λ y α) [ x / t ]≡ (Λ y β)
  V       : ∀{α β x y t} → x ≢ y → y NotFreeInTerm t
              → α [ x / t ]≡ β → (V y α) [ x / t ]≡ (V y β)

\end{code}

\todo{Move this elsewhere?}
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
  Λ/   : ∀{α β x y} → y NotFreeIn α → α [ x / varterm y ]≡ β → Λ x α ≈ Λ y β
  V    : ∀{α α′} → ∀ x → α ≈ α′ → V x α ≈ V x α′
  V/   : ∀{α β x y} → y NotFreeIn α → α [ x / varterm y ]≡ β → V x α ≈ V y β

\end{code}

Substitutions do not always exist. For example, there is no way of constructing
a formula for $(\forall y P x)[x/y]$. In general, $\alpha [x/t]$ exists only if
$t$ is \emph{free for} $x$ \emph{in} $\alpha$, meaning no variables in $t$
would become bound inside $alpha$. This can be formalised by using (with minor
modification) the rules of \cite{vandalen}.
\begin{code}

data _FreeFor_In_ (t : Term) (x : Variable) : Formula → Set where
  notfree : ∀{α} → x NotFreeIn α → t FreeFor x In α
  atom    : ∀ r us → t FreeFor x In atom r us
  _⇒_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ⇒ β
  _∧_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ∧ β
  _∨_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ∨ β
  Λ∣      : ∀ α → t FreeFor x In Λ x α
  V∣      : ∀ α → t FreeFor x In V x α
  Λ       : ∀ α y → y NotFreeInTerm t → t FreeFor x In α → t FreeFor x In Λ y α
  V       : ∀ α y → y NotFreeInTerm t → t FreeFor x In α → t FreeFor x In V y α

\end{code}
It will later be shown that, using the above definitions, there is a $\beta$
satisfying $\alpha [x/t]\equiv \beta$ if and only if $t$ is free for $x$ in
$\alpha$. \todo{Include this proof}

Finally, we define a proposition for a variable being \emph{fresh}, meaning it
appears nowhere (free or bound) in a formula. We later prove that if $x$ is
fresh in $\alpha$ then it is not free, and for every $y$, $x$ is free for $y$
in $\alpha$.
\begin{code}

data _FreshIn_ (x : Variable) : Formula → Set where
  atom : ∀{r ts} → x NotFreeInTerms ts  → x FreshIn (atom r ts)
  _⇒_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ⇒ β
  _∧_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ∧ β
  _∨_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ∨ β
  Λ    : ∀{α y} → x ≢ y → x FreshIn α → x FreshIn Λ y α
  V    : ∀{α y} → x ≢ y → x FreshIn α → x FreshIn V y α

\end{code}

\subsection{Computing substitutions}

The definitions above for variable substitution lead directly to a procedure
for computing substitutions. Given $\alpha$, $x$, $t$, and a proof that $t$ is
free for $x$ in $\alpha$, we compute a $\beta$ and a proof that
$\alpha[x/t] \equiv \beta$. The sigma (dependent sum) type can be used to
encapsulate both a value and a proof regarding that value.

First for vectors of terms, recurse through all function arguments, and replace
any variables equal to $x$ with $t$. In the code below, we do a case split on
the first term, and use a \inline{with} block to get the substitution for the
rest of the vector simultaneously, since this substitution is required in
either case.
\begin{code}

[_][_/_] : ∀{n} → (us : Vec Term n) → ∀ x t → Σ (Vec Term n) [ us ][ x / t ]≡_
[ [] ][ x / t ] = [] , []
[ u ∷ us ][ x / t ] with [ us ][ x / t ]
[ varterm y     ∷ us ][ x / t ] | vs , vspf with varEq x y
...    | yes refl = (t         ∷ vs) , (varterm≡     ∷ vspf)
...    | no  x≢y  = (varterm y ∷ vs) , (varterm≢ x≢y ∷ vspf)
[ functerm f ws ∷ us ][ x / t ] | vs , vspf with [ ws ][ x / t ]
...    | xs , xspf = (functerm f xs ∷ vs) , (functerm xspf ∷ vspf)

\end{code}

For formulae, a proof that $t$ is free for $x$ in the formula must be supplied.
The term $t$ is fixed by supplying such a proof, so for convenience of
notation, the proof is supplied in place of the term. In the following code we
will use names like \inline{x∉α} to denote proofs of `$x$ is not free in
$\alpha$`.
\begin{code}

_[_/_] : ∀{t} → ∀ α x → t FreeFor x In α → Σ Formula (α [ x / t ]≡_)
α [ x / notfree ¬x∉α ]          = α , notfree ¬x∉α
\end{code}
For atomic formulae, apply the above lemma.
\begin{code}
_[_/_] {t} (atom r ts) x tff    with [ ts ][ x / t ]
...                             | ts′ , tspf = atom r ts′ , atom r tspf
\end{code}
For the propositional connectives, the substitution is obtained recursively.
\begin{code}
(α ⇒ β) [ x / tffα ⇒ tffβ ]     with α [ x / tffα ] | β [ x / tffβ ]
...                             | α′ , αpf | β′ , βpf = α′ ⇒ β′ , αpf ⇒ βpf
(α ∧ β) [ x / tffα ∧ tffβ ]     with α [ x / tffα ] | β [ x / tffβ ]
...                             | α′ , αpf | β′ , βpf = α′ ∧ β′ , αpf ∧ βpf
(α ∨ β) [ x / tffα ∨ tffβ ]     with α [ x / tffα ] | β [ x / tffβ ]
...                             | α′ , αpf | β′ , βpf = α′ ∨ β′ , αpf ∨ βpf
\end{code}
For generalisation, check if $x$ is the quantifier, and if so do nothing.
Otherwise, recurse.
\begin{code}
Λ y α [ .y / Λ∣ .α ]            = Λ y α , Λ∣ y α
Λ y α [ x / Λ .α .y y∉t tffα ] with varEq x y
...                             | yes refl = Λ y α , Λ∣ y α
...                             | no  x≢y  with α [ x / tffα ]
...                                        | α′ , αpf = Λ y α′ , Λ x≢y y∉t αpf
V y α [ .y / V∣ .α ]            = V y α , V∣ y α
V y α [ x / V .α .y y∉t tffα ] with varEq x y
...                             | yes refl = V y α , V∣ y α
...                             | no  x≢y  with α [ x / tffα ]
...                                        | α′ , αpf = V y α′ , V x≢y y∉t αpf

\end{code}

\subsection{Decidability}

Variable freedom within a vector of terms is decidable, simply by searching
through the vector for occurences.
\begin{code}

_notFreeInTerms_ : ∀{n} → ∀ x → (ts : Vec Term n) → Dec (x NotFreeInTerms ts)
x notFreeInTerms [] = yes []
\end{code}
To check against a variable term, use the decidable equality of variables.
\begin{code}
x notFreeInTerms (varterm y ∷ ts) with varEq x y
...    | yes refl = no λ { (varterm x≢x ∷ _) → x≢x refl }
...    | no  x≢y  with x notFreeInTerms ts
...               | yes x∉ts = yes (varterm x≢y ∷ x∉ts)
...               | no ¬x∉ts = no λ { (_ ∷ x∉ts) → ¬x∉ts x∉ts }
\end{code}
To check against a function term, recurse over the arguments.
\begin{code}
x notFreeInTerms (functerm f us ∷ ts) with x notFreeInTerms us
...    | no ¬x∉us = no λ { (functerm x∉us ∷ _) → ¬x∉us x∉us }
...    | yes x∉us with x notFreeInTerms ts
...               | yes x∉ts = yes (functerm x∉us ∷ x∉ts)
...               | no ¬x∉ts = no λ { (_ ∷ x∉ts) → ¬x∉ts x∉ts }

\end{code}
Note that each case must check if $x$ is free in the remaining terms in the
vector. A shorter proof would do this check at the same time as doing a case
split on the first term, as was done for variable substitution in a vector of
terms above. However, if a term for which $x$ is free is found, it is not
necessary to continue recursing through the vector, so it is better
computationally not to do so.

The same logic can be used for a single term, calling the above function to
check function arguments. The proposition \inline{_NotFreeInTerms_} is defined
using \inline{All} and \inline{_NotFreeInTerm_}, so it is tempting to try to
first prove that the single term case is decidable, and then generalise to
vectors using the lemma that \inline{All} is decidable for decidable
predicates. However, this would not be structurally recursive, and so Agda
would not see this as terminating. Above, the case \mintinline{agda}{x
notFreeInTerms t ∷ ts} depends on the result of \inline{x notFreeInterms ts},
which is in fact primitively recursive. However, if it instead depended on the
result of \inline{all (x notFreeInTerm_) ts}, Agda cannot determine that
\inline{x notFreeInTerm_} will be applied only to arguments structurally
smaller than \inline{t ∷ ts}.
\begin{code}

_notFreeInTerm_ : (x : Variable) → (t : Term) → Dec (x NotFreeInTerm t)
x notFreeInTerm varterm y     with varEq x y
...                           | yes refl = no λ { (varterm x≢x) → x≢x refl }
...                           | no x≢y  = yes (varterm x≢y)
x notFreeInTerm functerm f ts with x notFreeInTerms ts
...                           | yes x∉ts = yes (functerm x∉ts)
...                           | no ¬x∉ts = no λ { (functerm x∉ts) → ¬x∉ts x∉ts }

\end{code}

Now for formulae, to determine if a variable is not free, we apply the above
for atoms, check recursively for the logical connectives, and check if the
variable is the quantifying variable for the quantifiers.
\begin{code}

_notFreeIn_ : (x : Variable) → (α : Formula) → Dec (x NotFreeIn α)
x notFreeIn atom r ts with x notFreeInTerms ts
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

\subsection{Generating fresh variables}

For the purposes of variable substitution (see above), we need a way to
generate a fresh variable for a given formula. Only finitely many variables
occur in a given term or formula, so there is a greatest (with respect to the
natural number indexing) variable occuring in each term or formula; all
variables greater than this are fresh. We first compute this variable for
terms, and then specialise to a single term, for termination reasons similar to
that of \inline{_notFreeInTerms_}. Note that for terms, there is no distinction
between being fresh and being not-free.
\todo{Explain \mintinline{agda}{Σ}}
\begin{code}

supFreeTerms : ∀{k} → (ts : Vec Term k) → Σ ℕ λ ⌈ts⌉ → ∀ n → ⌈ts⌉ < n
               → var n NotFreeInTerms ts
supFreeTerms [] = zero , λ _ _ → []
\end{code}
If the first term is a variable, check if its index is greater than the
greatest \todo{supremum} free variable of the rest of the terms. If not, use the
variable from the rest of the terms.
\begin{code}
supFreeTerms (varterm (var m) ∷ ts) with supFreeTerms ts
... | ⌈ts⌉ , tspf with ≤total m ⌈ts⌉
...               | less m≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    orderneq : ∀{n m} → n < m → var m ≢ var n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n
                    → All (var n NotFreeInTerm_) (varterm (var m) ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = varterm (orderneq (≤trans (sn≤sm m≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
\end{code}
Otherwise, use this variable.
\begin{code}
...               | more ⌈ts⌉≤m = m , notFreeIsm
  where
    orderneq : ∀{n m} → n < m → var m ≢ var n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIsm : ∀ n → m < n
                 → All (var n NotFreeInTerm_) (varterm (var m) ∷ ts)
    notFreeIsm n m<n = varterm (orderneq m<n)
                       ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤m) m<n)
\end{code}
If the first term is a function, then check if the greatest free variable in
its arguments is greater than the greatest free variable of the rest of the
terms. If not, use the variable from the rest of the terms.
\begin{code}
supFreeTerms (functerm f us     ∷ ts) with supFreeTerms us | supFreeTerms ts
... | ⌈us⌉ , uspf | ⌈ts⌉ , tspf with ≤total ⌈us⌉ ⌈ts⌉
...                             | less ⌈us⌉≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n
                    → All (var n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = functerm (uspf n (≤trans (sn≤sm ⌈us⌉≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
\end{code}
Otherwise, use the variable from the function's arguments.
\begin{code}
...                             | more ⌈ts⌉≤⌈us⌉ = ⌈us⌉ , notFreeIs⌈us⌉
  where
    notFreeIs⌈us⌉ : ∀ n → ⌈us⌉ < n
                    → All (var n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈us⌉ n ⌈us⌉<n = functerm (uspf n ⌈us⌉<n)
                             ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤⌈us⌉) ⌈us⌉<n)

\end{code}

\todo{Update for minFresh}
If the greatest variable occuring (free or bound) in $\alpha$ has
index $\lceil\alpha\rceil$, and $\beta$ has greatest variable with index
$\lceil\alpha\rceil$, then any variable with an index greater than
$\max\{\lceil\alpha\rceil, \lceil\alpha\rceil\}$ will be not free in $\alpha
\rightarrow \beta$. We therefore obtain infinitely many variables which are not
free in $\alpha \rightarrow \beta$. A similar process is followed for other
logical connectors.

Note that there will be variables which are bound, or which do not occur at
all, which are not generated by this process. If $x, y, z$ have indicies $0,
1,$ and $2$, then $\forall x \forall y R x y$ and $P y \lor \lnot P y$ will
both have $z$ as the least not-free variable generated.

\begin{code}

minFresh : ∀ α → Σ Variable λ ⌈α⌉ → ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn α
minFresh (atom r ts) with supFreeTerms ts
minFresh (atom r ts) | ⌈ts⌉ , tspf = var (suc ⌈ts⌉)
                                     , (λ n ⌈ts⌉≤n → atom (tspf n ⌈ts⌉≤n))
minFresh (α ⇒ β) with minFresh α | minFresh β
...              | ⌈α⌉ , αpf | ⌈β⌉ , βpf with ≤total (varidx ⌈α⌉) (varidx ⌈β⌉)
...                                      | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , freshIs⌈β⌉
  where
    freshIs⌈β⌉ : ∀ n → varidx ⌈β⌉ ≤ n → var n FreshIn (α ⇒ β)
    freshIs⌈β⌉ n ⌈β⌉≤n = αpf n (≤trans ⌈α⌉≤⌈β⌉ ⌈β⌉≤n) ⇒ βpf n ⌈β⌉≤n
...                                      | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn (α ⇒ β)
    freshIs⌈α⌉ n ⌈α⌉≤n = αpf n ⌈α⌉≤n ⇒ βpf n (≤trans ⌈β⌉≤⌈α⌉ ⌈α⌉≤n)
minFresh (α ∧ β) with minFresh α | minFresh β
...              | ⌈α⌉ , αpf | ⌈β⌉ , βpf with ≤total (varidx ⌈α⌉) (varidx ⌈β⌉)
...                                      | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , freshIs⌈β⌉
  where
    freshIs⌈β⌉ : ∀ n → varidx ⌈β⌉ ≤ n → var n FreshIn (α ∧ β)
    freshIs⌈β⌉ n ⌈β⌉≤n = αpf n (≤trans ⌈α⌉≤⌈β⌉ ⌈β⌉≤n) ∧ βpf n ⌈β⌉≤n
...                                      | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn (α ∧ β)
    freshIs⌈α⌉ n ⌈α⌉≤n = αpf n ⌈α⌉≤n ∧ βpf n (≤trans ⌈β⌉≤⌈α⌉ ⌈α⌉≤n)
minFresh (α ∨ β) with minFresh α | minFresh β
...              | ⌈α⌉ , αpf | ⌈β⌉ , βpf with ≤total (varidx ⌈α⌉) (varidx ⌈β⌉)
...                                      | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , freshIs⌈β⌉
  where
    freshIs⌈β⌉ : ∀ n → varidx ⌈β⌉ ≤ n → var n FreshIn (α ∨ β)
    freshIs⌈β⌉ n ⌈β⌉≤n = αpf n (≤trans ⌈α⌉≤⌈β⌉ ⌈β⌉≤n) ∨ βpf n ⌈β⌉≤n
...                                      | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn (α ∨ β)
    freshIs⌈α⌉ n ⌈α⌉≤n = αpf n ⌈α⌉≤n ∨ βpf n (≤trans ⌈β⌉≤⌈α⌉ ⌈α⌉≤n)
minFresh (Λ x@(var k) α) with minFresh α
...                      | ⌈α⌉ , αpf with ≤total (suc k) (varidx ⌈α⌉)
...                                  | less sk≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var n ≢ var m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn Λ x α
    freshIs⌈α⌉ n ⌈α⌉≤n = Λ (skNewLemma (≤trans sk≤⌈α⌉ ⌈α⌉≤n)) (αpf n ⌈α⌉≤n)
...                                  | more ⌈α⌉≤sk = var (suc k) , freshIssk
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var n ≢ var m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIssk : ∀ n → suc k ≤ n → var n FreshIn Λ x α
    freshIssk n sk≤n = Λ (skNewLemma sk≤n) (αpf n (≤trans ⌈α⌉≤sk sk≤n))
minFresh (V x@(var k) α) with minFresh α
...                      | ⌈α⌉ , αpf with ≤total (suc k) (varidx ⌈α⌉)
...                                  | less sk≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var n ≢ var m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn V x α
    freshIs⌈α⌉ n ⌈α⌉≤n = V (skNewLemma (≤trans sk≤⌈α⌉ ⌈α⌉≤n)) (αpf n ⌈α⌉≤n)
...                                    | more ⌈α⌉≤sk = var (suc k) , freshIssk
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var n ≢ var m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIssk : ∀ n → suc k ≤ n → var n FreshIn V x α
    freshIssk n sk≤n = V (skNewLemma sk≤n) (αpf n (≤trans ⌈α⌉≤sk sk≤n))

fresh : ∀ α → Σ Variable (_FreshIn α)
fresh α with minFresh α
...     | ⌈α⌉ , αpf = ⌈α⌉ , αpf (varidx ⌈α⌉) ≤refl

\end{code}

Given a formula $\alpha$, variable $x$, and term $t$, a similar process to the
one above produces a variable which is fresh (not free in $\alpha$, not equal
to $x$, and not in $t$).

\subsection{Lemata}

If a variable has been substituted by a term not involving that variable, then
the variable is not free in the resulting term.

\begin{code}

subNotFree : ∀{α x t β} → x NotFreeInTerm t → α [ x / t ]≡ β → x NotFreeIn β
subNotFree (varterm x≢x) (ident α x) = ⊥-elim (x≢x refl)
subNotFree x∉t (notfree x∉α)   = x∉α
subNotFree x∉t (atom r p)       = atom (termsLemma x∉t p)
  where
    termsLemma : ∀{n x t} {us vs : Vec Term n} → x NotFreeInTerm t
                      → [ us ][ x / t ]≡ vs → x NotFreeInTerms vs
    termsLemma x∉t []                  = []
    termsLemma x∉t (varterm≡ ∷ ps)     = x∉t ∷ termsLemma x∉t ps
    termsLemma x∉t (varterm≢ neq ∷ ps) = varterm neq ∷ termsLemma x∉t ps
    termsLemma x∉t (functerm sub ∷ ps) = functerm (termsLemma x∉t sub)
                                           ∷ termsLemma x∉t ps
subNotFree x∉t (pα ⇒ pβ)        = subNotFree x∉t pα ⇒ subNotFree x∉t pβ
subNotFree x∉t (pα ∧ pβ)        = subNotFree x∉t pα ∧ subNotFree x∉t pβ
subNotFree x∉t (pα ∨ pβ)        = subNotFree x∉t pα ∨ subNotFree x∉t pβ
subNotFree x∉t (Λ∣ y α)         = Λ∣ y α
subNotFree x∉t (Λ x≢y y∉t p)   = Λ _ (subNotFree x∉t p)
subNotFree x∉t (V∣ y α)         = V∣ y α
subNotFree x∉t (V x≢y y∉t p)   = V _ (subNotFree x∉t p)


freshNotFree : ∀{α x} → x FreshIn α → x NotFreeIn α
freshNotFree (atom x∉ts)   = atom x∉ts
freshNotFree (xfrα ⇒ xfrβ) = freshNotFree xfrα ⇒ freshNotFree xfrβ
freshNotFree (xfrα ∧ xfrβ) = freshNotFree xfrα ∧ freshNotFree xfrβ
freshNotFree (xfrα ∨ xfrβ) = freshNotFree xfrα ∨ freshNotFree xfrβ
freshNotFree (Λ _ xfrα)    = Λ _ (freshNotFree xfrα)
freshNotFree (V _ xfrα)    = V _ (freshNotFree xfrα)


freshFreeFor : ∀{α x y} → x FreshIn α → (varterm x) FreeFor y In α
freshFreeFor (atom _)      = atom _ _
freshFreeFor (xfrα ⇒ xfrβ) = freshFreeFor xfrα ⇒ freshFreeFor xfrβ
freshFreeFor (xfrα ∧ xfrβ) = freshFreeFor xfrα ∧ freshFreeFor xfrβ
freshFreeFor (xfrα ∨ xfrβ) = freshFreeFor xfrα ∨ freshFreeFor xfrβ
freshFreeFor (Λ x≢y xfrα)  = Λ _ _
                             (varterm λ { refl → x≢y refl }) (freshFreeFor xfrα)
freshFreeFor (V x≢y xfrα)  = V _ _
                             (varterm λ { refl → x≢y refl }) (freshFreeFor xfrα)

\end{code}

The result of $\alpha [ x / t ]$ should be a formula $\beta$ satisfying $\alpha [ x / t ]\equiv \beta$. Such a $\beta$ is computable.

\begin{code}

subInverse : ∀{ω α x β}
             → ω NotFreeIn α → α [ x / varterm ω ]≡ β → β [ ω / varterm x ]≡ α
subInverse _           (ident α x)    = ident α x
subInverse ω∉α         (notfree x∉α)  = notfree ω∉α
subInverse (atom x∉ts) (atom r subts) = atom r (termsLemma x∉ts subts)
  where
    termsLemma : ∀{n x ω} {us vs : Vec Term n} → ω NotFreeInTerms us
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
