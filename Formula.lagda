\section{Formula.lagda}

\begin{code}

module Formula where

open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Decidable
open import Nat
open import Vec

\end{code}

We adopt the definitions from Proof and Computation (Schwichteberg). In
particular, there are countably many variables, and countably many function
symbols of each (natural) airty.

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
search.

Terms are either variables, or functions applied to the appropriate number of
arguments.

\begin{code}

data Term : Set where
  varterm  : (x : Variable) → Term
  functerm : (f : Function) → (ts : Vec Term (Function.arity f)) → Term

\end{code}

Relation symbols work the same way as Function symbols.

\begin{code}

record Relation : Set where
  constructor mkrel
  field
    idx   : ℕ
    arity : ℕ

\end{code}

We now define atoms (prime formulae), and the logical connectives, using
$\Lambda$ and $V$ in place of $\forall$ and $\exists$, since $\forall$ is
reserved by Agda.

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

A variable is shown to be bound in a formula with an obvious recursive
definition. It is bound inside a quantification over a subformula $\alpha$ if
either it is the quantification variable, or else if it is bound in $\alpha$.
Separate constructors are given for these. A variable is bound inside an atom
if it appears nowhere within that atom, meaning it is not within the terms that
the relation is operating on. We define a lemma for this, as a function's terms
may include further functions, and so on. For a given term, $x$ is bound within
that term if that term is a variable other than $x$, or otherwise if the term
is a function, and $x$ is bound in all arguments.

\begin{code}

infix 300 _NotFreeInTerm_ _NotFreeInTerms_ _NotFreeIn_ [_][_/_]≡_ _[_/_]≡_

data _NotFreeInTerm_ (x : Variable) : Term → Set

_NotFreeInTerms_ : ∀{n} → Variable → Vec Term n → Set
x NotFreeInTerms ts = All (x NotFreeInTerm_) ts

data _NotFreeInTerm_ (x : Variable) where
  varterm  : ∀{y} → x ≢ y → x NotFreeInTerm (varterm y)
  functerm : ∀{f} {us : Vec Term (Function.arity f)}
               → x NotFreeInTerms us → x NotFreeInTerm (functerm f us)

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
of replacing terms with terms is not needed for natural deduction. The
reasoning is similar to that of the bound variable check above, and a lemma is
used for the same reasons. Inside a vector of terms, wherever $x$ occurs, it is
replaced with $t$. Any variable distinct from $x$ is left unchanged.

\begin{code}

data [_][_/_]≡_ : ∀{n} → Vec Term n → Variable → Term → Vec Term n → Set

data ⟨_⟩[_/_]≡_ : Term → Variable → Term → Term → Set where
  varterm≡ : ∀{x t} → ⟨ varterm x ⟩[ x / t ]≡ t
  varterm≢ : ∀{x t y} → x ≢ y → ⟨ varterm y ⟩[ x / t ]≡ varterm y
  functerm : ∀{x t f us vs}
              → [ us ][ x  / t ]≡ vs → ⟨ functerm f us ⟩[ x / t ]≡ functerm f vs

data [_][_/_]≡_ where
  []  : ∀{x t} → [ [] ][ x / t ]≡ []
  _∷_ : ∀{x t u v n} {us vs : Vec Term n}
        → ⟨ u ⟩[ x / t ]≡ v → [ us ][ x / t ]≡ vs → [ u ∷ us ][ x / t ]≡ (v ∷ vs)

\end{code}

An extra constructor `ident' is defined, giving the case that replacing $x$
with $x$ yields the original formula. This case is actually provable from the
others. However, in practice it is the case we usually want to use, and so
would like Agda's proof search to find it easily.

Variable replacement for a quantified formula has three cases. Consider the
replacement $(\forall y \alpha) [ x / t ]$ (the existential case is identical):

\begin{enumerate}
\item If the variable being replaced is the quantification variable ($x = y$),
      then the formula is unchanged.
\item If the variable being replaced is not the quantification variable
      ($x \neq y$), and $t$ is free for $x$ in $\forall y \alpha$ ($x \not\in
      FV(t)$), then the replacement simply occurs inside the quantification (
      $(\forall y \alpha) [ x / t ] = \forall y (\alpha [ x / t ])$).
\item Otherwise, the quantifying variable must be renamed. We require a fresh
      variable $\omega$ which is not free in $\alpha$, which differs from $x$,
      and which is not in $t$. Then the replacement is
      $(\forall y \alpha) [ x / t ]
       = \forall \omega (\alpha [ y / \omega ][ x / t ])$).
\end{enumerate}

We provide a constructor for each case. Note that the third case means that
replacement is not unique.

If $y$ is not free in $\alpha$, and $beta$ is $\alpha [ x / y ]$ then it we
would like $alpha$ to be $\beta [ y / x ]$, so that renaming to fresh variables
is invertible. However, due to the third case above, $\beta [ y / x ]$ may
differ from $\alpha$ in the names of its bound variables. A simple solition to
this problem is to add the constructor `inverse' as below.

\begin{code}

data _[_/_]≡_ : Formula → Variable → Term → Formula → Set where
  ident   : ∀ α x → α [ x / varterm x ]≡ α
  inverse : ∀{α β x y} → y NotFreeIn α → α [ x / varterm y ]≡ β → β [ y / varterm x ]≡ α
  atom  : ∀{x t}
            → (r : Relation) → {xs ys : Vec Term (Relation.arity r)}
            → [ xs ][ x / t ]≡ ys → (atom r xs) [ x / t ]≡ (atom r ys)
  _⇒_   : ∀{α α′ β β′ x t}
            → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ⇒ β) [ x / t ]≡ (α′ ⇒ β′)
  _∧_   : ∀{α α′ β β′ x t}
            → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∧ β) [ x / t ]≡ (α′ ∧ β′)
  _∨_   : ∀{α α′ β β′ x t}
            → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∨ β) [ x / t ]≡ (α′ ∨ β′)
  Λ∣    : ∀{t} → (x : Variable) → (α : Formula) → (Λ x α) [ x / t ]≡ (Λ x α)
  V∣    : ∀{t} → (x : Variable) → (α : Formula) → (V x α) [ x / t ]≡ (V x α)
  Λ     : ∀{α β x v t} → v ≢ x → x NotFreeInTerm t → α [ v / t ]≡ β → (Λ x α) [ v / t ]≡ (Λ x β)
  V     : ∀{α β x v t} → v ≢ x → x NotFreeInTerm t → α [ v / t ]≡ β → (V x α) [ v / t ]≡ (V x β)
  Λ/    : ∀{α β γ x v t ω} → ω NotFreeIn α → v ≢ ω → ω NotFreeInTerm t
          → α [ x / varterm ω ]≡ β → β [ v / t ]≡ γ → (Λ x α) [ v / t ]≡ (Λ ω γ)
  V/    : ∀{α β γ x v t ω} → ω NotFreeIn α → v ≢ ω → ω NotFreeInTerm t
          → α [ x / varterm ω ]≡ β → β [ v / t ]≡ γ → (V x α) [ v / t ]≡ (V ω γ)

\end{code}

The notion of a variable being fresh, for use in a replacement as $\omega$ is
in the last two constructors, is encapsulated below.

\begin{code}

record FreshVar (α : Formula) (x : Variable) (t : Term) : Set where
  constructor mkfreshvar
  field
    var         : Variable
    notFree     : var NotFreeIn α
    new         : x ≢ var
    replaceable : var NotFreeInTerm t


\end{code}


The constructors `inverse', `$\Lambda{}$/', and `V/', are convenient, but not
ideal. A more thourough treatment would involve defining a notion of ``formula
equivalence up to renaming of bound variables'' mutually with variable
replacement, and replace those constructors with one such as $\alpha \sim \beta
\rightarrow \beta [ x / t ]\equiv \gamma \rightarrow \alpha [ x / t ]\equiv
\gamma$. This entails some extra work to prove that `inverse' (and some later
lemmae) hold, however, and the details not necessary for natural deduction.


It remains to prove that equality of formulae is decidable. This follows from
the fact that formulae are inductively defined. The proof is obtained by case
analysis, using lemmae on the types used to construct formulae. The unremarkable
proofs are ommitted from the latex-typeset form of this file, except for
equality of natural numbers, which is included for illustrative purposes.

Lemmas:

\begin{code}
natEq : Decidable≡ ℕ
natEq zero zero = yes refl
natEq zero (suc m) = no (λ ())
natEq (suc n) zero = no (λ ())
natEq (suc n) (suc m) with natEq n m
...                   | yes refl = yes refl
...                   | no  neq  = no φ
                                   where φ : _
                                         φ refl = neq refl
\end{code}

\begin{code}
varEq : Decidable≡ Variable
\end{code}
(Proof Omitted.)
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
\end{code}
(Proof Omitted.)
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
\end{code}
(Proof Omitted.)
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
\end{code}
(Proof Omitted.)
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
\end{code}
(Proof Omitted.)
\AgdaHide{
\begin{code}
termEq (varterm x) (varterm y) with varEq x y
...                             | yes refl = yes refl
...                             | no  neq  = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (varterm _) (functerm _ _) = no λ ()
termEq (functerm _ _) (varterm _) = no (λ ())
termEq (functerm (mkfunc n .0) []) (functerm (mkfunc m .0) []) with natEq n m
termEq (functerm (mkfunc n _) []) (functerm (mkfunc .n _) []) | yes refl = yes refl
termEq (functerm (mkfunc n _) []) (functerm (mkfunc m _) []) | no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (functerm (mkfunc _ .0) []) (functerm (mkfunc _ .(suc _)) (_ ∷ _)) = no (λ ())
termEq (functerm (mkfunc _ .(suc _)) (_ ∷ _)) (functerm (mkfunc _ .0) []) = no (λ ())
termEq (functerm (mkfunc n (suc k)) (x ∷ xs)) (functerm (mkfunc m (suc j)) (y ∷ ys)) with (natEq n m) , (natEq k j)
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (y ∷ ys)) | yes refl , yes refl with termEq (functerm (mkfunc n j) xs) (functerm (mkfunc n j) ys)
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (y ∷ .xs)) | yes refl , yes refl | yes refl with termEq x y
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (.x ∷ .xs)) | yes refl , yes refl | yes refl | yes refl = yes refl
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (y ∷ .xs)) | yes refl , yes refl | yes refl | no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (y ∷ ys)) | yes refl , yes refl | no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (functerm (mkfunc n (suc k)) (x ∷ xs)) (functerm (mkfunc m (suc j)) (y ∷ ys)) | _ , no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (functerm (mkfunc n (suc k)) (x ∷ xs)) (functerm (mkfunc m (suc j)) (y ∷ ys)) | no neq , _ = no φ
                                             where φ : _
                                                   φ refl = neq refl
\end{code}
}

\begin{code}
formulaEq : Decidable≡ Formula
\end{code}
(Proof Omitted.)
\AgdaHide{
\begin{code}
formulaEq (atom r xs) (atom s ys) with natEq (Relation.arity r) (Relation.arity s)
...                               | yes refl with (relEq r s) , (vecEq termEq xs ys)
...                                          | yes refl , yes refl = yes refl
...                                          | _ , no neq = no φ
                                                            where φ : _
                                                                  φ refl = neq refl
...                                          | no neq , _ = no φ
                                                            where φ : _
                                                                  φ refl = neq refl
formulaEq (atom r xs) (atom s ys) | no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
formulaEq (α ⇒ β) (γ ⇒ δ) with (formulaEq α γ) , (formulaEq β δ)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (α ∧ β) (γ ∧ δ) with (formulaEq α γ) , (formulaEq β δ)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (α ∨ β) (γ ∨ δ) with (formulaEq α γ) , (formulaEq β δ)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (Λ x α) (Λ y β) with (varEq x y) , (formulaEq α β)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (V x α) (V y β) with (varEq x y) , (formulaEq α β)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (atom r x) (β ⇒ β₁)   = no (λ ())
formulaEq (atom r x) (β ∧ β₁)   = no (λ ())
formulaEq (atom r x) (β ∨ β₁)   = no (λ ())
formulaEq (atom r x) (Λ x₁ β)   = no (λ ())
formulaEq (atom r x) (V x₁ β)   = no (λ ())
formulaEq (α ⇒ α₁)   (atom r x) = no (λ ())
formulaEq (α ⇒ α₁)   (β ∧ β₁)   = no (λ ())
formulaEq (α ⇒ α₁)   (β ∨ β₁)   = no (λ ())
formulaEq (α ⇒ α₁)   (Λ x β)    = no (λ ())
formulaEq (α ⇒ α₁)   (V x β)    = no (λ ())
formulaEq (α ∧ α₁)   (atom r x) = no (λ ())
formulaEq (α ∧ α₁)   (β ⇒ β₁)   = no (λ ())
formulaEq (α ∧ α₁)   (β ∨ β₁)   = no (λ ())
formulaEq (α ∧ α₁)   (Λ x β)    = no (λ ())
formulaEq (α ∧ α₁)   (V x β)    = no (λ ())
formulaEq (α ∨ α₁)   (atom r x) = no (λ ())
formulaEq (α ∨ α₁)   (β ⇒ β₁)   = no (λ ())
formulaEq (α ∨ α₁)   (β ∧ β₁)   = no (λ ())
formulaEq (α ∨ α₁)   (Λ x β)    = no (λ ())
formulaEq (α ∨ α₁)   (V x β)    = no (λ ())
formulaEq (Λ x α)   (atom r x₁) = no (λ ())
formulaEq (Λ x α)   (β ⇒ β₁)    = no (λ ())
formulaEq (Λ x α)   (β ∧ β₁)    = no (λ ())
formulaEq (Λ x α)   (β ∨ β₁)    = no (λ ())
formulaEq (Λ x α)   (V x₁ β)    = no (λ ())
formulaEq (V x α)   (atom r x₁) = no (λ ())
formulaEq (V x α)   (β ⇒ β₁)    = no (λ ())
formulaEq (V x α)   (β ∧ β₁)    = no (λ ())
formulaEq (V x α)   (β ∨ β₁)    = no (λ ())
formulaEq (V x α)   (Λ x₁ β)    = no (λ ())

\end{code}
}
\begin{code}

--------------------------------------------------------------------------------

-- Machine-proven lemmae
repNotFreeTerms : ∀{n x t} {us vs : Vec Term n} → x NotFreeInTerm t → [ us ][ x / t ]≡ vs → x NotFreeInTerms vs
repNotFreeTerms {.0} {x} {t} {[]} {.[]} xnft [] = []
repNotFreeTerms {.(suc _)} {.x₁} {_} {varterm x₁ ∷ us} {.(_ ∷ _)} xnft (varterm≡ ∷ rep) = xnft ∷ repNotFreeTerms xnft rep
repNotFreeTerms {.(suc _)} {x} {t} {varterm x₁ ∷ us} {.(varterm x₁ ∷ _)} xnft (varterm≢ x₂ ∷ rep) = varterm x₂ ∷ repNotFreeTerms xnft rep
repNotFreeTerms {.(suc _)} {x} {t} {functerm f ts ∷ us} {.(functerm f _ ∷ _)} xnft (functerm x₁ ∷ rep) = functerm (repNotFreeTerms xnft x₁) ∷ repNotFreeTerms xnft rep

repNotFree : ∀{α x t β} → x NotFreeInTerm t → α [ x / t ]≡ β → x NotFreeIn β
repNotFree {α} {x} {t} {β} xnft (inverse xnfβ rep) = xnfβ
repNotFree {atom r ts} {x₁} {.(varterm x₁)} {.(atom r ts)} (varterm x) (ident .(atom r ts) x₁) = ⊥-elim (x refl)
repNotFree {atom r ts} {x} {t} {.(atom r _)} xnft (atom .r x₁) = atom (repNotFreeTerms xnft x₁)
repNotFree {α ⇒ α₁} {x₁} {.(varterm x₁)} {.(α ⇒ α₁)} (varterm x) (ident .(α ⇒ α₁) x₁) = ⊥-elim (x refl)
repNotFree {α ⇒ α₁} {x} {t} {.(_ ⇒ _)} xnft (rep ⇒ rep₁) = repNotFree xnft rep ⇒ repNotFree xnft rep₁
repNotFree {α ∧ α₁} {x₁} {.(varterm x₁)} {.(α ∧ α₁)} (varterm x) (ident .(α ∧ α₁) x₁) = ⊥-elim (x refl)
repNotFree {α ∧ α₁} {x} {t} {.(_ ∧ _)} xnft (rep ∧ rep₁) = repNotFree xnft rep ∧ repNotFree xnft rep₁
repNotFree {α ∨ α₁} {x₁} {.(varterm x₁)} {.(α ∨ α₁)} (varterm x) (ident .(α ∨ α₁) x₁) = ⊥-elim (x refl)
repNotFree {α ∨ α₁} {x} {t} {.(_ ∨ _)} xnft (rep ∨ rep₁) = repNotFree xnft rep ∨ repNotFree xnft rep₁
repNotFree {Λ x₁ α} {x₂} {.(varterm x₂)} {.(Λ x₁ α)} (varterm x) (ident .(Λ x₁ α) x₂) = ⊥-elim (x refl)
repNotFree {Λ x₁ α} {.x₁} {t} {.(Λ x₁ α)} xnft (Λ∣ .x₁ .α) = Λ∣ x₁ α
repNotFree {Λ x₁ α} {x} {t} {.(Λ x₁ _)} xnft (Λ x₂ x₃ rep) = Λ x₁ (repNotFree xnft rep)
repNotFree {Λ x₁ α} {x} {t} {.(Λ _ _)} xnft (Λ/ x₂ x₃ x₄ rep rep₁) = Λ _ (repNotFree xnft rep₁)
repNotFree {V x₁ α} {x₂} {.(varterm x₂)} {.(V x₁ α)} (varterm x) (ident .(V x₁ α) x₂) = ⊥-elim (x refl)
repNotFree {V x₁ α} {.x₁} {t} {.(V x₁ α)} xnft (V∣ .x₁ .α) = V∣ x₁ α
repNotFree {V x₁ α} {x} {t} {.(V x₁ _)} xnft (V x₂ x₃ rep) = V x₁ (repNotFree xnft rep)
repNotFree {V x₁ α} {x} {t} {.(V _ _)} xnft (V/ x₂ x₃ x₄ rep rep₁) = V _ (repNotFree xnft rep₁)

--------------------------------------------------------------------------------


_notFreeInTerms_ : ∀{n} → (x : Variable) → (ts : Vec Term n) → Dec (x NotFreeInTerms ts)
x notFreeInTerms []                   = yes []
x notFreeInTerms (t ∷ ts)             with x notFreeInTerms ts
x notFreeInTerms (t ∷ ts)             | no ¬rst = no φ
  where
    φ : ¬(All (x NotFreeInTerm_) (t ∷ ts))
    φ (_ ∷ rst) = ¬rst rst
x notFreeInTerms (varterm y ∷ ts)     | yes rst with varEq x y
x notFreeInTerms (varterm .x ∷ ts)    | yes rst | yes refl = no φ
  where
    φ : ¬(All (x NotFreeInTerm_) (varterm x ∷ ts))
    φ (varterm x≢x ∷ _) = x≢x refl
x notFreeInTerms (varterm y ∷ ts)     | yes rst | no x≢y = yes (varterm x≢y ∷ rst)
x notFreeInTerms (functerm f us ∷ ts) | yes rst with x notFreeInTerms us
x notFreeInTerms (functerm f us ∷ ts) | yes rst | yes uspf = yes (functerm uspf ∷ rst)
x notFreeInTerms (functerm f us ∷ ts) | yes rst | no ¬uspf = no φ
  where
    φ : ¬(All (x NotFreeInTerm_) (functerm f us ∷ ts))
    φ (functerm uspf ∷ _) = ¬uspf uspf


_notFreeInTerm_ : (x : Variable) → (t : Term) → Dec (x NotFreeInTerm t)
x notFreeInTerm t with x notFreeInTerms (t ∷ [])
x notFreeInTerm t | yes (pf ∷ []) = yes pf
x notFreeInTerm t | no npf        = no λ z → npf (z ∷ [])


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


supfreeterms : ∀{k} → (ts : Vec Term k) → Σ ℕ λ ⌈ts⌉ → ∀ n → ⌈ts⌉ < n → mkvar n NotFreeInTerms ts
supfreeterms [] = zero , λ _ _ → []
supfreeterms (varterm (mkvar m) ∷ ts) with supfreeterms ts
... | ⌈ts⌉ , tspf with max m ⌈ts⌉
...               | less m≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    orderneq : ∀{n m} → n < m → mkvar m ≢ mkvar n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n → All (mkvar n NotFreeInTerm_) (varterm (mkvar m) ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = varterm (orderneq (≤trans (sn≤sm m≤⌈ts⌉) ⌈ts⌉<n)) ∷ tspf n ⌈ts⌉<n
...               | more ⌈ts⌉≤m = m , notFreeIsm
  where
    orderneq : ∀{n m} → n < m → mkvar m ≢ mkvar n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIsm : ∀ n → m < n → All (mkvar n NotFreeInTerm_) (varterm (mkvar m) ∷ ts)
    notFreeIsm n m<n = varterm (orderneq m<n) ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤m) m<n)
supfreeterms (functerm f us     ∷ ts) with supfreeterms us | supfreeterms ts
... | ⌈us⌉ , uspf | ⌈ts⌉ , tspf with max ⌈us⌉ ⌈ts⌉
...                             | less ⌈us⌉≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n → All (mkvar n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = functerm (uspf n (≤trans (sn≤sm ⌈us⌉≤⌈ts⌉) ⌈ts⌉<n)) ∷ tspf n ⌈ts⌉<n
...                             | more ⌈ts⌉≤⌈us⌉ = ⌈us⌉ , notFreeIs⌈us⌉
  where
    notFreeIs⌈us⌉ : ∀ n → ⌈us⌉ < n → All (mkvar n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈us⌉ n ⌈us⌉<n = functerm (uspf n ⌈us⌉<n) ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤⌈us⌉) ⌈us⌉<n)


supfreeterm : ∀ t → Σ ℕ λ ⌈t⌉ → ∀ n → ⌈t⌉ < n → mkvar n NotFreeInTerm t
supfreeterm t with supfreeterms (t ∷ [])
supfreeterm t | s , pfs = s , notFreeIss
  where
    notFreeIss : ∀ n → s < n → mkvar n NotFreeInTerm t
    notFreeIss n s<n with pfs n s<n
    notFreeIss n s<n | pf ∷ [] = pf


-- No guarantee that this notFree is tight - in fact for the V and Λ cases it is
-- not tight if the quantifier is the greatest variable (and does not have index
-- zero)
supfree : ∀ α → Σ ℕ λ ⌈α⌉ → ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn α
supfree (atom r ts) with supfreeterms ts
supfree (atom r ts) | ⌈ts⌉ , tspf = ⌈ts⌉ , λ n ⌈ts⌉<n → atom (tspf n ⌈ts⌉<n)
supfree (α ⇒ β) with supfree α | supfree β
supfree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supfree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ⇒ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ⇒ βpf n ⌈β⌉<n
supfree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ⇒ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ⇒ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supfree (α ∧ β) with supfree α | supfree β
supfree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supfree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ∧ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∧ βpf n ⌈β⌉<n
supfree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ∧ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∧ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supfree (α ∨ β) with supfree α | supfree β
supfree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supfree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ∨ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∨ βpf n ⌈β⌉<n
supfree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ∨ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∨ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supfree (Λ x α) with supfree α
supfree (Λ x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → Λ x (αpf n ⌈α⌉<n)
supfree (V x α) with supfree α
supfree (V x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → V x (αpf n ⌈α⌉<n)


freshVar : ∀ α x t → FreshVar α x t
freshVar α (mkvar n) t with supfree α | supfreeterm t
... | ⌈α⌉ , αpf | ⌈t⌉ , tpf with max n ⌈α⌉ | max n ⌈t⌉ | max ⌈α⌉ ⌈t⌉
...   | less n≤⌈α⌉ | less n≤⌈t⌉ | less ⌈α⌉≤⌈t⌉ = mkfreshvar (mkvar (suc ⌈t⌉)) notFree new replaceable
  where
    notFree : mkvar (suc ⌈t⌉) NotFreeIn α
    notFree = αpf (suc ⌈t⌉) (sn≤sm ⌈α⌉≤⌈t⌉)
    new : mkvar n ≢ mkvar (suc ⌈t⌉)
    new refl = ⊥-elim (¬<refl n≤⌈t⌉)
    replaceable : mkvar (suc ⌈t⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈t⌉) (sn≤sm ≤refl)
...   | less n≤⌈α⌉ | less n≤⌈t⌉ | more ⌈t⌉≤⌈α⌉ = mkfreshvar (mkvar (suc ⌈α⌉)) notFree new replaceable
  where
    notFree : mkvar (suc ⌈α⌉) NotFreeIn α
    notFree = αpf (suc ⌈α⌉) (sn≤sm ≤refl)
    new : mkvar n ≢ mkvar (suc ⌈α⌉)
    new refl = ¬<refl n≤⌈α⌉
    replaceable : mkvar (suc ⌈α⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈α⌉) (sn≤sm ⌈t⌉≤⌈α⌉)
...   | less n≤⌈α⌉ | more ⌈t⌉≤n | _            = mkfreshvar (mkvar (suc ⌈α⌉)) notFree new replaceable
  where
    notFree : mkvar (suc ⌈α⌉) NotFreeIn α
    notFree = αpf (suc ⌈α⌉) (sn≤sm ≤refl)
    new : mkvar n ≢ mkvar (suc ⌈α⌉)
    new refl = ¬<refl n≤⌈α⌉
    replaceable : mkvar (suc ⌈α⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈α⌉) (≤trans (sn≤sm ⌈t⌉≤n) (sn≤sm n≤⌈α⌉))
...   | more ⌈α⌉≤n | less n≤⌈t⌉ | _            = mkfreshvar (mkvar (suc ⌈t⌉)) notFree new replaceable
  where
    notFree : mkvar (suc ⌈t⌉) NotFreeIn α
    notFree = αpf (suc ⌈t⌉) (≤trans (sn≤sm ⌈α⌉≤n) (sn≤sm n≤⌈t⌉))
    new : mkvar n ≢ mkvar (suc ⌈t⌉)
    new refl = ¬<refl n≤⌈t⌉
    replaceable : mkvar (suc ⌈t⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈t⌉) (sn≤sm ≤refl)
...   | more ⌈α⌉≤n | more ⌈t⌉≤n | _            = mkfreshvar (mkvar (suc n)) notFree new replaceable
  where
    notFree : mkvar (suc n) NotFreeIn α
    notFree = αpf (suc n) (sn≤sm ⌈α⌉≤n)
    new : mkvar n ≢ mkvar (suc n)
    new ()
    replaceable : mkvar (suc n) NotFreeInTerm t
    replaceable = tpf (suc n) (sn≤sm ⌈t⌉≤n)


[_][_/_] : ∀{n} → (us : Vec Term n) → ∀ x t → Σ (Vec Term n) λ vs → [ us ][ x / t ]≡ vs
[ [] ][ x / t ] = [] , []
[ u ∷ us ][ x / t ] with [ us ][ x / t ]
[ varterm y     ∷ us ][ x / t ] | vs , [us][x/t]≡vs with varEq x y
... | yes refl = t ∷ vs , (varterm≡ ∷ [us][x/t]≡vs)
... | no x≡y   = varterm y ∷ vs , (varterm≢ x≡y ∷ [us][x/t]≡vs)
[ functerm f ws ∷ us ][ x / t ] | vs , [us][x/t]≡vs with [ ws ][ x / t ]
... | xs , [ws][x/t]≡xs = functerm f xs ∷ vs , (functerm [ws][x/t]≡xs ∷ [us][x/t]≡vs)

-- Make sure to use the nicer substitutions for quantification where possible
{-# TERMINATING #-}
_[_/_] : ∀ α x t → Σ Formula (α [ x / t ]≡_)
atom r us [ x / t ] with [ us ][ x / t ]
atom r us [ x / t ] | vs , [us][x/t]≡vs = atom r vs , atom r [us][x/t]≡vs
(α ⇒ β)   [ x / t ] with α [ x / t ] | β [ x / t ]
(α ⇒ β)   [ x / t ] | α′ , α[x/t]≡α′ | β′ , β[x/t]≡β′ = α′ ⇒ β′ , α[x/t]≡α′ ⇒ β[x/t]≡β′
(α ∧ β)   [ x / t ] with α [ x / t ] | β [ x / t ]
(α ∧ β)   [ x / t ] | α′ , α[x/t]≡α′ | β′ , β[x/t]≡β′ = α′ ∧ β′ , α[x/t]≡α′ ∧ β[x/t]≡β′
(α ∨ β)   [ x / t ] with α [ x / t ] | β [ x / t ]
(α ∨ β)   [ x / t ] | α′ , α[x/t]≡α′ | β′ , β[x/t]≡β′ = α′ ∨ β′ , α[x/t]≡α′ ∨ β[x/t]≡β′
Λ  y α    [ x / t ] with varEq x y | y notFreeInTerm t
Λ .x α    [ x / t ] | yes refl | _       = Λ x α , Λ∣ x α
Λ  y α    [ x / t ] | no x≢y   | yes xnf with α [ x / t ]
Λ  y α    [ x / t ] | no x≢y   | yes xnf | α′ , α[x/t]≡α′ = Λ y α′ , Λ x≢y xnf α[x/t]≡α′
Λ  y α    [ x / t ] | no x≢y   | no  xf  with freshVar α x t
Λ  y α    [ x / t ] | no x≢y   | no  xf  | mkfreshvar ω ωnfα x≢ω ωnft with α [ y / varterm ω ]
Λ  y α    [ x / t ] | no x≢y   | no xf   | mkfreshvar ω ωnfα x≢ω ωnft | β , α[y/ω]≡β with β [ x / t ]
Λ  y α    [ x / t ] | no x≢y   | no xf   | mkfreshvar ω ωnfα x≢ω ωnft | β , α[y/ω]≡β | γ , β[x/t]≡γ
                    = Λ ω γ , Λ/ ωnfα x≢ω ωnft α[y/ω]≡β β[x/t]≡γ
V  y α    [ x / t ] with varEq x y | y notFreeInTerm t
V .x α    [ x / t ] | yes refl | _       = V x α , V∣ x α
V  y α    [ x / t ] | no x≢y   | yes xnf with α [ x / t ]
V  y α    [ x / t ] | no x≢y   | yes xnf | α′ , α[x/t]≡α′ = V y α′ , V x≢y xnf α[x/t]≡α′
V  y α    [ x / t ] | no x≢y   | no  xf  with freshVar α x t
V  y α    [ x / t ] | no x≢y   | no  xf  | mkfreshvar ω ωnfα x≢ω ωnft with α [ y / varterm ω ]
V  y α    [ x / t ] | no x≢y   | no xf   | mkfreshvar ω ωnfα x≢ω ωnft | β , α[y/ω]≡β with β [ x / t ]
V  y α    [ x / t ] | no x≢y   | no xf   | mkfreshvar ω ωnfα x≢ω ωnft | β , α[y/ω]≡β | γ , β[x/t]≡γ
                    = V ω γ , V/ ωnfα x≢ω ωnft α[y/ω]≡β β[x/t]≡γ
\end{code}
