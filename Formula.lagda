\begin{code}

module Formula where

open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Decidable
open import Nat
open import Vec

\end{code}

We adopt the definitions from Proof and Computation (Schwichteberg)
\todo{cite}. In particular, there are countably many variables, and there are
countably many function symbols of each (natural) airty. Function symbols of
different arities with the same index are considered different.

\begin{code}

record Variable : Set where
  constructor mkvar
  field
    idx : ℕ

record Function : Set where
  constructor mkfunc
  field
    idx   : ℕ
    arity : ℕ

\end{code}

Note that the indices are natural numbers. While it seems equivalent and more
useful to index using strings, strings are not supported by Agda's proof
search. Internally, strings are not recursively defined as the natural numbers
are; instead it is a postulated type which is bound to string literals.

Terms are either variables, or functions applied to the appropriate number of
arguments (zero for constants).

\begin{code}

data Term : Set where
  varterm  : (x : Variable) → Term
  functerm : (f : Function) → (ts : Vec Term (Function.arity f)) → Term

\end{code}

Relation symbols work the same way as function symbols.

\begin{code}

record Relation : Set where
  constructor mkrel
  field
    idx   : ℕ
    arity : ℕ

\end{code}

We now define atoms (prime formulae), and the logical connectives, using
$\bigwedge$ and $\bigvee$ in place of $\forall$ and $\exists$, since $\forall$
is reserved by Agda.

\todo{Rename $\Lambda$ and $V$}
\begin{code}

data Formula : Set where
  atom   : (r : Relation) → (ts : Vec Term (Relation.arity r)) → Formula
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

The following notion of a Scheme is more general than usual; instead of using
placeholder symbols which are replaced by formulae, a Scheme is just
constructed from a function from formulae to a formula. This is much easier to
work with.

\begin{code}

record Scheme : Set where
  constructor scheme
  field
    idx   : String
    arity : ℕ
    inst  : Vec Formula arity → Formula

\end{code}

For a given term, $x$ is bound within that term if that term is a variable
other than $x$, or otherwise if the term is a function, and $x$ is bound in all
arguments, which can be checked by applying \inline{All} to this definition.

\begin{code}

_NotFreeInTerms_ : ∀{n} → Variable → Vec Term n → Set

data _NotFreeInTerm_ (x : Variable) : Term → Set where
  varterm  : ∀{y} → x ≢ y → x NotFreeInTerm (varterm y)
  functerm : ∀{f} {us : Vec Term (Function.arity f)}
               → x NotFreeInTerms us → x NotFreeInTerm (functerm f us)

x NotFreeInTerms ts = All (x NotFreeInTerm_) ts

\end{code}

A variable is shown to be bound in a formula with the obvious recursive
definition. It is bound inside a quantification over a subformula $\alpha$ if
either it is the quantification variable, or else if it is bound in $\alpha$.
Separate constructors are given for these. A variable is bound inside an atom
if it is not free within that atom, meaning it is not free in the terms that
the relation is operating on.

\begin{code}

data _NotFreeIn_ : Variable → Formula → Set where
  atom : ∀{x r} {ts : Vec Term (Relation.arity r)}
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
replacing all instances of a variable $x$ with term $t$. The more general case
of replacing terms with terms is not needed for natural deduction.

Inside a vector of terms, wherever $x$ occurs, it is replaced with $t$. Any
variable distinct from $x$ is left unchanged. For a function, $x$ is replaced
with $t$ in all of the arguments.

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

Now, for formulae:
\todo{Should these be $\equiv$?}
\begin{code}

data _[_/_]≡_ : Formula → Variable → Term → Formula → Set where
\end{code}
The \inline{ident} constructor gives the case that replacing $x$ with $x$
yields the original formula. This case is actually provable from the others,
However, in practice it is the case we usually want to use, and so we would
like Agda's proof search to find it easily.
\begin{code}
  ident   : ∀ α x → α [ x / varterm x ]≡ α
\end{code}
The propositional cases are similar to those of the \inline{_NotFreeIn_} type
above.
\begin{code}
  atom    : ∀{x t}
              → (r : Relation) → {xs ys : Vec Term (Relation.arity r)}
              → [ xs ][ x / t ]≡ ys → (atom r xs) [ x / t ]≡ (atom r ys)
  _⇒_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ⇒ β) [ x / t ]≡ (α′ ⇒ β′)
  _∧_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∧ β) [ x / t ]≡ (α′ ∧ β′)
  _∨_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∨ β) [ x / t ]≡ (α′ ∨ β′)
\end{code}
Variable substitution for a quantified formula has three cases, with the first
two also being similar to their counterparts in \inline{_NotFreeIn_}. If $x$ is
the quantification variable, then the formula is unchanged.
\begin{code}
  Λ∣      : ∀{t} → (x : Variable) → (α : Formula) → (Λ x α) [ x / t ]≡ (Λ x α)
  V∣      : ∀{t} → (x : Variable) → (α : Formula) → (V x α) [ x / t ]≡ (V x α)
\end{code}
If $x$ is not the quantification variable and $t$ is free for $x$ in in the
formula ($x$ is not free in term $t$), then the substitution simply occurs
inside the quantification.
\begin{code}
  Λ       : ∀{α β x v t} → v ≢ x → x NotFreeInTerm t
              → α [ v / t ]≡ β → (Λ x α) [ v / t ]≡ (Λ x β)
  V       : ∀{α β x v t} → v ≢ x → x NotFreeInTerm t
              → α [ v / t ]≡ β → (V x α) [ v / t ]≡ (V x β)
\end{code}
Otherwise, the quantifying variable must be renamed. We require a variable
$\omega$ which is not free in $\alpha$, which differs from $x$, and which is
not in $t$. Since there are infinitely many such $\omega$, substitution is not
unique. After replacing the quantifier with $omega$, we proceed as in the
previous case.
\begin{code}
  Λ/      : ∀{α β γ x v t ω} → ω NotFreeIn α → v ≢ ω → ω NotFreeInTerm t
              → α [ x / varterm ω ]≡ β → β [ v / t ]≡ γ
              → (Λ x α) [ v / t ]≡ (Λ ω γ)
  V/      : ∀{α β γ x v t ω} → ω NotFreeIn α → v ≢ ω → ω NotFreeInTerm t
              → α [ x / varterm ω ]≡ β → β [ v / t ]≡ γ
              → (V x α) [ v / t ]≡ (V ω γ)
\end{code}
Finally, if $y$ is not free in $\alpha$, and $\alpha [ x / y ]\equiv \beta$
then it we would like $\beta [ y / x ]\equiv \alpha$, so that renaming to
not-free variables is invertible. However, due to the third case above, $\beta
[ y / x ]$ may differ from $\alpha$ in the names of its bound variables. A
simple solution to this problem is to add a constructor for this.
\begin{code}
  inverse : ∀{α β x y} → y NotFreeIn α
              → α [ x / varterm y ]≡ β → β [ y / varterm x ]≡ α

\end{code}

The constructors \inline{inverse}, \mintinline{agda}{Λ/}, and \inline{V/}, are
convenient, but not ideal. A more thourough treatment would involve defining a
notion of ``formula equivalence up to renaming of bound variables'' mutually
with variable substitution, and replace those constructors with one such as
$\alpha \sim \beta \rightarrow \beta [ x / t ]\equiv \gamma \rightarrow \alpha
[ x / t ]\equiv \gamma$. This entails some extra work to prove that lemata like
\inline{inverse} hold, however, and the details not necessary for natural
deduction.

We encapsulate the notion of a variable being fresh, for use in a substitution
as $\omega$ is in the constructors \mintinline{agda}{Λ/} and \inline{V/}.

\begin{code}

record FreshVar (α : Formula) (x : Variable) (t : Term) : Set where
  constructor mkfreshvar
  field
    var         : Variable
    notFree     : var NotFreeIn α
    new         : x ≢ var
    replaceable : var NotFreeInTerm t

\end{code}

It remains to prove that equality of formulae is decidable. This follows from
the fact that formulae are inductively defined. The proof is obtained by case
analysis, using lemata on the types used to construct formulae. The unremarkable
proofs are omitted from the latex-typeset form of this file, except for
equality of natural numbers, which is included for illustrative purposes.

\begin{code}

natEq : Decidable≡ ℕ
natEq zero zero = yes refl
natEq zero (suc m) = no λ ()
natEq (suc n) zero = no λ ()
natEq (suc n) (suc m) with natEq n m
...                   | yes refl = yes refl
...                   | no  neq  = no φ
                                   where φ : _
                                         φ refl = neq refl

\end{code}
\begin{code}

varEq : Decidable≡ Variable
-- Proof omitted

\end{code}
\AgdaHide{
\begin{code}

varEq (mkvar n) (mkvar m) with natEq n m
...                       | yes refl = yes refl
...                       | no  neq  = no φ
                                       where φ : _
                                             φ refl = neq refl

\end{code}
}
\begin{code}

relEq : Decidable≡ Relation
-- Proof omitted

\end{code}
\AgdaHide{
\begin{code}

relEq (mkrel n j) (mkrel m k) with natEq n m
...                           | no  neq  = no φ
                                            where φ : _
                                                  φ refl = neq refl
...                           | yes refl with natEq j k
...                                      | yes refl = yes refl
...                                      | no  neq  = no φ
                                                      where φ : _
                                                            φ refl = neq refl

\end{code}
}
\begin{code}

funcEq : Decidable≡ Function
-- Proof omitted

\end{code}
\AgdaHide{
\begin{code}

funcEq (mkfunc n j) (mkfunc m k) with natEq n m
...                              | no  neq  = no φ
                                              where φ : _
                                                    φ refl = neq refl
...                              | yes refl with natEq j k
...                                         | yes refl = yes refl
...                                         | no  neq  = no φ
                                                         where φ : _
                                                               φ refl = neq refl

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
...                        | no  neq  = no φ
                                        where φ : _
                                              φ refl = neq refl
...                        | yes refl with vecEq eq xs ys
...                                   | yes refl = yes refl
...                                   | no  neq  = no φ
                                                   where φ : _
                                                         φ refl = neq refl

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
...                                    | no x≢y   = no φ
                                                    where φ : _
                                                          φ refl = x≢y refl
termEq (varterm x)     (functerm f ts) = no λ ()
termEq (functerm f ts) (varterm x)     = no λ ()
termEq (functerm f []) (functerm g []) with funcEq f g
...                                    | yes refl = yes refl
...                                    | no f≢g   = no φ
                                                    where φ : _
                                                          φ refl = f≢g refl
termEq (functerm f []) (functerm g (_ ∷ _)) = no λ ()
termEq (functerm f (_ ∷ _)) (functerm g []) = no λ ()
termEq
  (functerm (mkfunc n (suc j)) (u ∷ us)) (functerm (mkfunc m (suc k)) (v ∷ vs))
  with natEq j k
... | no n≢m   = no φ
                 where φ : _
                       φ refl = n≢m refl
... | yes refl with termEq u v
...   | no u≢v   = no φ
                   where φ : _
                         φ refl = u≢v refl
...   | yes refl
        with termEq (functerm (mkfunc n j) us) (functerm (mkfunc m k) vs)
...     | yes refl = yes refl
...     | no neq   = no φ
                     where φ : _
                           φ refl = neq refl

\end{code}
}
\begin{code}

formulaEq : Decidable≡ Formula
-- Proof omitted

\end{code}
\AgdaHide{
\begin{code}

formulaEq (atom r xs) (atom s ys)
    with natEq (Relation.arity r) (Relation.arity s)
... | no neq = no φ
               where φ : _
                     φ refl = neq refl
... | yes refl with (relEq r s) | (vecEq termEq xs ys)
...            | yes refl | yes refl = yes refl
...            | _        | no neq   = no φ
                                       where φ : _
                                             φ refl = neq refl
...            | no neq   | _        = no φ
                                       where φ : _
                                             φ refl = neq refl
formulaEq (α ⇒ β) (γ ⇒ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
formulaEq (α ∧ β) (γ ∧ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
formulaEq (α ∨ β) (γ ∨ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
formulaEq (Λ x α) (Λ y β) with (varEq x y) | (formulaEq α β)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
formulaEq (V x α) (V y β) with (varEq x y) | (formulaEq α β)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
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

Variable freedom within a vector of terms is decidable, simply by searching
through the vector for occurences. To check against a variable term, use the
decidable equality of variables. To check against a function term, recurse over
the arguments.

\begin{code}

_notFreeInTerms_ : ∀{n} → (x : Variable) → (ts : Vec Term n)
                   → Dec (x NotFreeInTerms ts)
x notFreeInTerms [] = yes []
x notFreeInTerms (varterm y ∷ ts) with varEq x y
... | yes refl = no φ
                 where φ : _
                       φ (varterm nrefl ∷ _) = nrefl refl
... | no x≢y   with x notFreeInTerms ts
...            | yes xnfts = yes (varterm x≢y ∷ xnfts)
...            | no xfts   = no φ
                             where φ : _
                                   φ (_ ∷ xnfts) = xfts xnfts
x notFreeInTerms (functerm f us ∷ ts) with x notFreeInTerms us
... | no xfus   = no φ
                  where φ : _
                        φ (functerm xnfus ∷ _) = xfus xnfus
... | yes xnfus with x notFreeInTerms ts
...             | yes xnfts = yes (functerm xnfus ∷ xnfts)
...             | no xfts   = no φ
                              where φ : _
                                    φ (_ ∷ xnfts) = xfts xnfts

\end{code}

The same logic can be used for a single term, calling the above function to
check function arguments. The proposition \inline{_NotFreeInTerms_} is defined
using \inline{All} and \inline{_NotFreeInTerm_}, so it is tempting to try to
first prove that the single term case is decidable, and then generalise to
vectors using the lemma that \inline{All} is decidable for decidable
predicates. However, this would not be structurally recursive, and so Agda
would not see this as terminating. Above, the case \mintinline{agda}{x
notFreeInTerms t ∷ ts} depends on the result of \inline{x notFreeInterms ts},
which is in fact primitively recursive. However, if it instead depended on the
result of \inline{all (x notFreeInTerm) ts} \todo{finish}

\begin{code}

_notFreeInTerm_ : (x : Variable) → (t : Term) → Dec (x NotFreeInTerm t)
x notFreeInTerm varterm y     with varEq x y
...                           | yes refl = no φ
                                           where φ : _
                                                 φ (varterm x≢x) = x≢x refl
...                           | no x≢y  = yes (varterm x≢y)
x notFreeInTerm functerm f ts with x notFreeInTerms ts
...                           | yes xnfts = yes (functerm xnfts)
...                           | no ¬xnfts = no φ
                                            where
                                              φ : _
                                              φ (functerm xnfts) = ¬xnfts xnfts

\end{code}

Now for formulae, to determine if a variable is not free, we apply the above
for atoms, check recursively for the logical connectives, and check if the
variable is the quantifying variable for the quantifiers.

\begin{code}

_notFreeIn_ : (x : Variable) → (α : Formula) → Dec (x NotFreeIn α)
x notFreeIn atom r ts with x notFreeInTerms ts
x notFreeIn atom r ts | yes bdts = yes (atom bdts)
x notFreeIn atom r ts | no ¬bdts = no φ
                                   where
                                     φ : ¬(x NotFreeIn atom r ts)
                                     φ (atom bdts) = ¬bdts bdts
x notFreeIn (α ⇒ β)   with x notFreeIn α | x notFreeIn β
x notFreeIn (α ⇒ β)   | yes αbd | yes βbd = yes (αbd ⇒ βbd)
x notFreeIn (α ⇒ β)   | _       | no ¬βbd = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ⇒ β))
                                              φ (αbd ⇒ βbd) = ¬βbd βbd
x notFreeIn (α ⇒ β)   | no ¬αbd | _       = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ⇒ β))
                                              φ (αbd ⇒ βbd) = ¬αbd αbd
x notFreeIn (α ∧ β)   with x notFreeIn α | x notFreeIn β
x notFreeIn (α ∧ β)   | yes αbd | yes βbd = yes (αbd ∧ βbd)
x notFreeIn (α ∧ β)   | _       | no ¬βbd = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ∧ β))
                                              φ (αbd ∧ βbd) = ¬βbd βbd
x notFreeIn (α ∧ β)   | no ¬αbd | _       = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ∧ β))
                                              φ (αbd ∧ βbd) = ¬αbd αbd
x notFreeIn (α ∨ β)   with x notFreeIn α | x notFreeIn β
x notFreeIn (α ∨ β)   | yes αbd | yes βbd = yes (αbd ∨ βbd)
x notFreeIn (α ∨ β)   | _       | no ¬βbd = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ∨ β))
                                              φ (αbd ∨ βbd) = ¬βbd βbd
x notFreeIn (α ∨ β)   | no ¬αbd | _       = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ∨ β))
                                              φ (αbd ∨ βbd) = ¬αbd αbd
x notFreeIn Λ  y α    with varEq x y
x notFreeIn Λ .x α    | yes refl = yes (Λ∣ x α)
x notFreeIn Λ  y α    | no x≢y with x notFreeIn α
x notFreeIn Λ  y α    | no x≢y | yes αbd = yes (Λ y αbd)
x notFreeIn Λ  y α    | no x≢y | no ¬αbd = no φ
                                           where
                                             φ : ¬(x NotFreeIn Λ y α)
                                             φ (Λ∣ x α) = x≢y refl
                                             φ (Λ y αbd) = ¬αbd αbd
x notFreeIn V  y α    with varEq x y
x notFreeIn V .x α    | yes refl = yes (V∣ x α)
x notFreeIn V  y α    | no x≢y with x notFreeIn α
x notFreeIn V  y α    | no x≢y | yes αbd = yes (V y αbd)
x notFreeIn V  y α    | no x≢y | no ¬αbd = no φ
                                           where
                                             φ : ¬(x NotFreeIn V y α)
                                             φ (V∣ x α) = x≢y refl
                                             φ (V y αbd) = ¬αbd αbd

\end{code}

For the purposes of variable substitution (see above), we need a way to
generate a not-free variable for a given formula. Only finitely many variables
occur in a given term or formula, so there is a greatest (with respect to the
natural number indexing) free variable in each term or formula; all variables
greater than this are not free.

\begin{code}

supFreeTerms : ∀{k} → (ts : Vec Term k) → Σ ℕ λ ⌈ts⌉ → ∀ n → ⌈ts⌉ < n
               → mkvar n NotFreeInTerms ts
supFreeTerms [] = zero , λ _ _ → []
supFreeTerms (varterm (mkvar m) ∷ ts) with supFreeTerms ts
... | ⌈ts⌉ , tspf with max m ⌈ts⌉
...               | less m≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    orderneq : ∀{n m} → n < m → mkvar m ≢ mkvar n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n
                    → All (mkvar n NotFreeInTerm_) (varterm (mkvar m) ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = varterm (orderneq (≤trans (sn≤sm m≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
...               | more ⌈ts⌉≤m = m , notFreeIsm
  where
    orderneq : ∀{n m} → n < m → mkvar m ≢ mkvar n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIsm : ∀ n → m < n
                 → All (mkvar n NotFreeInTerm_) (varterm (mkvar m) ∷ ts)
    notFreeIsm n m<n = varterm (orderneq m<n)
                       ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤m) m<n)
supFreeTerms (functerm f us     ∷ ts) with supFreeTerms us | supFreeTerms ts
... | ⌈us⌉ , uspf | ⌈ts⌉ , tspf with max ⌈us⌉ ⌈ts⌉
...                             | less ⌈us⌉≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n
                    → All (mkvar n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = functerm (uspf n (≤trans (sn≤sm ⌈us⌉≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
...                             | more ⌈ts⌉≤⌈us⌉ = ⌈us⌉ , notFreeIs⌈us⌉
  where
    notFreeIs⌈us⌉ : ∀ n → ⌈us⌉ < n
                    → All (mkvar n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈us⌉ n ⌈us⌉<n = functerm (uspf n ⌈us⌉<n)
                             ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤⌈us⌉) ⌈us⌉<n)

supFreeTerm : ∀ t → Σ ℕ λ ⌈t⌉ → ∀ n → ⌈t⌉ < n → mkvar n NotFreeInTerm t
supFreeTerm t with supFreeTerms (t ∷ [])
supFreeTerm t | s , pfs = s , notFreeIss
  where
    notFreeIss : ∀ n → s < n → mkvar n NotFreeInTerm t
    notFreeIss n s<n with pfs n s<n
    notFreeIss n s<n | pf ∷ [] = pf

\end{code}

If the greatest variable occuring (free or bound) in $\alpha$ has
index $\lceil\alpha\rceil$, and $\beta$ has greatest variable with index
$\lceil\alpha\rceil$, then any variable with an index greater than
$\max\{\lceil\alpha\rceil, \lceil\alpha\rceil\}$ will be not free in $\alpha
\rightarrow \beta$. We therefore obtain infinitely many variables which are not
free in $\alpha \rightarrow \beta$. A similar process is followed for other
logical connectors.

Note that there will be variables which bound, or which do not occur at all,
which are not generated by this process. If $x, y, z$ have indicies $0, 1,$ and
$2$, then $\forall x \forall y R x y$ and $P y \lor \lnot P y$ will both have
$z$ as the least not-free variable generated.

\begin{code}

supFree : ∀ α → Σ ℕ λ ⌈α⌉ → ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn α
supFree (atom r ts) with supFreeTerms ts
supFree (atom r ts) | ⌈ts⌉ , tspf = ⌈ts⌉ , λ n ⌈ts⌉<n → atom (tspf n ⌈ts⌉<n)
supFree (α ⇒ β) with supFree α | supFree β
supFree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supFree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ⇒ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ⇒ βpf n ⌈β⌉<n
supFree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ⇒ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ⇒ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supFree (α ∧ β) with supFree α | supFree β
supFree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supFree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ∧ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∧ βpf n ⌈β⌉<n
supFree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ∧ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∧ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supFree (α ∨ β) with supFree α | supFree β
supFree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supFree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ∨ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∨ βpf n ⌈β⌉<n
supFree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ∨ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∨ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supFree (Λ x α) with supFree α
supFree (Λ x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → Λ x (αpf n ⌈α⌉<n)
supFree (V x α) with supFree α
supFree (V x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → V x (αpf n ⌈α⌉<n)

\end{code}

Given a formula $\alpha$, variable $x$, and term $t$, a similar process to the
one above produces a variable which is fresh (not free in $\alpha$, not equal
to $x$, and not in $t$).

\begin{code}

freshVar : ∀ α x t → FreshVar α x t
freshVar α (mkvar n) t with supFree α | supFreeTerm t
... | ⌈α⌉ , αpf | ⌈t⌉ , tpf with max n ⌈α⌉ | max n ⌈t⌉ | max ⌈α⌉ ⌈t⌉
...   | less n≤⌈α⌉ | less n≤⌈t⌉ | less ⌈α⌉≤⌈t⌉ = mkfreshvar
                                                   (mkvar (suc ⌈t⌉))
                                                   notFree new replaceable
  where
    notFree : mkvar (suc ⌈t⌉) NotFreeIn α
    notFree = αpf (suc ⌈t⌉) (sn≤sm ⌈α⌉≤⌈t⌉)
    new : mkvar n ≢ mkvar (suc ⌈t⌉)
    new refl = ⊥-elim (¬<refl n≤⌈t⌉)
    replaceable : mkvar (suc ⌈t⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈t⌉) (sn≤sm ≤refl)
...   | less n≤⌈α⌉ | less n≤⌈t⌉ | more ⌈t⌉≤⌈α⌉ = mkfreshvar
                                                   (mkvar (suc ⌈α⌉))
                                                   notFree new replaceable
  where
    notFree : mkvar (suc ⌈α⌉) NotFreeIn α
    notFree = αpf (suc ⌈α⌉) (sn≤sm ≤refl)
    new : mkvar n ≢ mkvar (suc ⌈α⌉)
    new refl = ¬<refl n≤⌈α⌉
    replaceable : mkvar (suc ⌈α⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈α⌉) (sn≤sm ⌈t⌉≤⌈α⌉)
...   | less n≤⌈α⌉ | more ⌈t⌉≤n | _            = mkfreshvar
                                                   (mkvar (suc ⌈α⌉))
                                                   notFree new replaceable
  where
    notFree : mkvar (suc ⌈α⌉) NotFreeIn α
    notFree = αpf (suc ⌈α⌉) (sn≤sm ≤refl)
    new : mkvar n ≢ mkvar (suc ⌈α⌉)
    new refl = ¬<refl n≤⌈α⌉
    replaceable : mkvar (suc ⌈α⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈α⌉) (≤trans (sn≤sm ⌈t⌉≤n) (sn≤sm n≤⌈α⌉))
...   | more ⌈α⌉≤n | less n≤⌈t⌉ | _            = mkfreshvar
                                                   (mkvar (suc ⌈t⌉))
                                                   notFree new replaceable
  where
    notFree : mkvar (suc ⌈t⌉) NotFreeIn α
    notFree = αpf (suc ⌈t⌉) (≤trans (sn≤sm ⌈α⌉≤n) (sn≤sm n≤⌈t⌉))
    new : mkvar n ≢ mkvar (suc ⌈t⌉)
    new refl = ¬<refl n≤⌈t⌉
    replaceable : mkvar (suc ⌈t⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈t⌉) (sn≤sm ≤refl)
...   | more ⌈α⌉≤n | more ⌈t⌉≤n | _            = mkfreshvar
                                                   (mkvar (suc n))
                                                   notFree new replaceable
  where
    notFree : mkvar (suc n) NotFreeIn α
    notFree = αpf (suc n) (sn≤sm ⌈α⌉≤n)
    new : mkvar n ≢ mkvar (suc n)
    new ()
    replaceable : mkvar (suc n) NotFreeInTerm t
    replaceable = tpf (suc n) (sn≤sm ⌈t⌉≤n)

\end{code}

The result of $\alpha [ x / t ]$ should be a formula $\beta$ satisfying $\alpha [ x / t ]\equiv \beta$. Such a $\beta$ is computable.

\begin{code}

[_][_/_] : ∀{n} → (us : Vec Term n) → ∀ x t → Σ (Vec Term n) λ vs
           → [ us ][ x / t ]≡ vs
[ [] ][ x / t ] = [] , []
[ varterm y ∷ us ][ x / t ] with [ us ][ x / t ]
... | vs , [us][x/t]≡vs with varEq x y
...   | yes refl = (t ∷ vs) , (varterm≡ ∷ [us][x/t]≡vs)
...   | no x≢y   = (varterm y ∷ vs) , (varterm≢ x≢y ∷ [us][x/t]≡vs)
[ functerm f ws ∷ us ][ x / t ] with [ us ][ x / t ]
... | vs , [us][x/t]≡vs with [ ws ][ x / t ]
...   | xs , [ws][x/t]≡xs = (functerm f xs ∷ vs)
                            , (functerm [ws][x/t]≡xs ∷ [us][x/t]≡vs)

\end{code}

While there is a general constructor for variable substitution which works in
all cases, we avoid unnecessary renaming of bound variables by using the other
constructors where possible.

\begin{code}

{-# TERMINATING #-}
_[_/_] : ∀ α x t → Σ Formula (α [ x / t ]≡_)
atom r us [ x / t ] with [ us ][ x / t ]
... | vs , [us][x/t]≡vs = atom r vs , atom r [us][x/t]≡vs
(α ⇒ β)   [ x / t ] with α [ x / t ] | β [ x / t ]
... | α′ , α[x/t]≡α′ | β′ , β[x/t]≡β′ = α′ ⇒ β′ , α[x/t]≡α′ ⇒ β[x/t]≡β′
(α ∧ β)   [ x / t ] with α [ x / t ] | β [ x / t ]
... | α′ , α[x/t]≡α′ | β′ , β[x/t]≡β′ = α′ ∧ β′ , α[x/t]≡α′ ∧ β[x/t]≡β′
(α ∨ β)   [ x / t ] with α [ x / t ] | β [ x / t ]
... | α′ , α[x/t]≡α′ | β′ , β[x/t]≡β′ = α′ ∨ β′ , α[x/t]≡α′ ∨ β[x/t]≡β′
Λ y α     [ x / t ] with varEq x y | y notFreeInTerm t
... | yes refl | _       = Λ x α , Λ∣ x α
... | no x≢y   | yes xnf with α [ x / t ]
...   | α′ , α[x/t]≡α′ = Λ y α′ , Λ x≢y xnf α[x/t]≡α′
Λ  y α    [ x / t ] | no x≢y   | no  xf  with freshVar α x t
... | mkfreshvar ω ωnfα x≢ω ωnft with α [ y / varterm ω ]
...   | β , α[y/ω]≡β with β [ x / t ]
...     | γ , β[x/t]≡γ = Λ ω γ , Λ/ ωnfα x≢ω ωnft α[y/ω]≡β β[x/t]≡γ
V y α     [ x / t ] with varEq x y | y notFreeInTerm t
... | yes refl | _       = V x α , V∣ x α
... | no x≢y   | yes xnf with α [ x / t ]
...   | α′ , α[x/t]≡α′ = V y α′ , V x≢y xnf α[x/t]≡α′
V  y α    [ x / t ] | no x≢y   | no  xf  with freshVar α x t
... | mkfreshvar ω ωnfα x≢ω ωnft with α [ y / varterm ω ]
...   | β , α[y/ω]≡β with β [ x / t ]
...     | γ , β[x/t]≡γ = V ω γ , V/ ωnfα x≢ω ωnft α[y/ω]≡β β[x/t]≡γ

\end{code}

The proof above is declared to be terminating with a pragma. This is necessary
because of the substitution constructor which uses bound variable renaming. In
this case, to compute $\forall y \alpha [ x / t ]$, we first compute a fresh
variable $\omega$, and compute a $\beta$ satisfying $\alpha [ y / \omega
]\equiv \beta$. Then the substitution is done on $\beta$, by computing a
$\gamma$ satisfying $\beta [ x / t ]\equiv \gamma$. However, Agda does not see
this as structurally recursive, as there is no guarantee that $\beta$ is
structurally smaller than $\forall y \alpha$.

\todo{Offer solutions}


\subsection{Lemma}

If a variable has been replaced with a term not involving that variable, then
the variable is not free in the resulting term.

\begin{code}

subNotFreeTerms : ∀{n x t} {us vs : Vec Term n} → x NotFreeInTerm t
                  → [ us ][ x / t ]≡ vs → x NotFreeInTerms vs
subNotFreeTerms xnft []                  = []
subNotFreeTerms xnft (varterm≡ ∷ ps)     = xnft ∷ subNotFreeTerms xnft ps
subNotFreeTerms xnft (varterm≢ neq ∷ ps) = varterm neq ∷ subNotFreeTerms xnft ps
subNotFreeTerms xnft (functerm sub ∷ ps) = functerm (subNotFreeTerms xnft sub)
                                           ∷ subNotFreeTerms xnft ps

subNotFree : ∀{α x t β} → x NotFreeInTerm t → α [ x / t ]≡ β → x NotFreeIn β
subNotFree (varterm x≢x) (ident   _    _) = ⊥-elim (x≢x refl)
subNotFree _             (inverse xnfβ _) = xnfβ
subNotFree xnft (atom r p)       = atom (subNotFreeTerms xnft p)
subNotFree xnft (pα ⇒ pβ)        = subNotFree xnft pα ⇒ subNotFree xnft pβ
subNotFree xnft (pα ∧ pβ)        = subNotFree xnft pα ∧ subNotFree xnft pβ
subNotFree xnft (pα ∨ pβ)        = subNotFree xnft pα ∨ subNotFree xnft pβ
subNotFree xnft (Λ∣ y α)         = Λ∣ y α
subNotFree xnft (Λ x≢y ynft p)   = Λ _ (subNotFree xnft p)
subNotFree xnft (Λ/ _ _ _ p₁ p₂) = Λ _ (subNotFree xnft p₂)
subNotFree xnft (V∣ y α)         = V∣ y α
subNotFree xnft (V x≢y ynft p)   = V _ (subNotFree xnft p)
subNotFree xnft (V/ _ _ _ p₁ p₂) = V _ (subNotFree xnft p₂)

\end{code}
