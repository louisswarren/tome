\section{Formula.lagda}

\begin{code}

module Formula where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Vec
open import Decidable

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
  varterm  : Variable → Term
  functerm : (f : Function) → Vec Term (Function.arity f) → Term

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
  atom   : (r : Relation) → Vec Term (Relation.arity r) → Formula
  _⇒_    : Formula  → Formula → Formula
  _∧_    : Formula  → Formula → Formula
  _∨_    : Formula  → Formula → Formula
  Λ      : Variable → Formula → Formula
  V      : Variable → Formula → Formula

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

data _BoundInTerms_ (x : Variable) : ∀{n} → Vec Term n → Set where
  []    : x BoundInTerms []
  var∉  : ∀{n} {xs : Vec Term n}
            → (y : Variable)
            → x ≢ y
            → x BoundInTerms xs
            → x BoundInTerms (varterm y ∷ xs)
  func∉ : ∀{n} {xs : Vec Term n}
            → (f : Function) → {us : Vec Term (Function.arity f)}
            → x BoundInTerms us
            → x BoundInTerms xs
            → x BoundInTerms (functerm f us ∷ xs)

data _BoundIn_ : Variable → Formula → Set where
  atom : ∀{t r} {xs : Vec Term (Relation.arity r)}
                  → t BoundInTerms xs → t BoundIn (atom r xs)
  _⇒_  : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ⇒ β)
  _∧_  : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ∧ β)
  _∨_  : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ∨ β)
  Λ∣   : ∀ x α    → x BoundIn Λ x α
  V∣   : ∀ x α    → x BoundIn V x α
  Λ    : ∀{t α}   → ∀ x → t BoundIn α → t BoundIn Λ x α
  V    : ∀{t α}   → ∀ x → t BoundIn α → t BoundIn V x α

\end{code}

We define what it means for a formula $\beta$ to be obtained from $\alpha$ by
replacing all instances of a variable $x$ with term $t$. The reasoning is
similar to that of the bound variable check above, and a lemma is used for the
same reasons. Inside a vector of terms, wherever $x$ occurs, it is replaced
with $t$. Any variable distinct from $x$ is left unchanged.

An extra constructor `ident' is defined, giving the case that replacing $x$
with $x$ yields the original formula. This case is actually provable from the
others. However, in practice it is the case we usually want to use, and so
would like Agda's proof search to find it easily.

\begin{code}

data [_][_/_]≡_ : ∀{n} → Vec Term n → Variable → Term → Vec Term n → Set where
  []   : ∀{x t} → [ [] ][ x / t ]≡ []
  var≡ : ∀{n t} {xs ys : Vec Term n}
           → (x : Variable)
           → [ xs ][ x / t ]≡ ys
           → [ varterm x ∷ xs ][ x / t ]≡ (t ∷ ys)
  var≢ : ∀{n x t} {xs ys : Vec Term n}
           → (v : Variable)
           → x ≢ v
           → [ xs ][ x / t ]≡ ys
           → [ varterm v ∷ xs ][ x / t ]≡ (varterm v ∷ ys)
  func : ∀{n x t} {xs ys : Vec Term n}
           → (f : Function) → ∀{us vs}
           → [ us ][ x / t ]≡ vs
           → [ xs ][ x / t ]≡ ys
           → [ functerm f us ∷ xs ][ x / t ]≡ (functerm f vs ∷ ys)

data _[_/_]≡_ : Formula → Variable → Term → Formula → Set where
  ident : ∀ α x → α [ x / varterm x ]≡ α
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
  Λ     : ∀{α β x v t} → v ≢ x → α [ v / t ]≡ β → (Λ x α) [ v / t ]≡ (Λ x β)
  V     : ∀{α β x v t} → v ≢ x → α [ v / t ]≡ β → (V x α) [ v / t ]≡ (V x β)


\end{code}

It remains to prove that equality of formulae is decidable. This follows from
the fact that formulae are inductively defined. The proof is obtained by case
analysis, and is ommitted from the latex-typeset form of this file.

\begin{code}

formulaEq : Decidable≡ Formula

\end{code}

\AgdaHide{
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

varEq : Decidable≡ Variable
varEq (mkvar n) (mkvar m) with natEq n m
...                       | yes refl = yes refl
...                       | no  neq  = no φ
                                       where φ : _
                                             φ refl = neq refl

relEq : Decidable≡ Relation
relEq (mkrel n j) (mkrel m k) with natEq n m
...                           | no  neq  = no φ
                                            where φ : _
                                                  φ refl = neq refl
...                           | yes refl with natEq j k
...                                      | yes refl = yes refl
...                                      | no  neq  = no φ
                                                      where φ : _
                                                            φ refl = neq refl

funcEq : Decidable≡ Function
funcEq (mkfunc n j) (mkfunc m k) with natEq n m
...                              | no  neq  = no φ
                                              where φ : _
                                                    φ refl = neq refl
...                              | yes refl with natEq j k
...                                         | yes refl = yes refl
...                                         | no  neq  = no φ
                                                         where φ : _
                                                               φ refl = neq refl

vecEq : ∀{n} {A : Set} → Decidable≡ A → Decidable≡ (Vec A n)
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

{-# TERMINATING #-}
termEq : Decidable≡ Term
termEq (varterm x) (varterm y) with varEq x y
...                            | yes refl = yes refl
...                            | no  neq  = no φ
                                            where φ : _
                                                  φ refl = neq refl
termEq (varterm x) (functerm f xs) = no (λ ())
termEq (functerm f xs) (varterm x) = no (λ ())
termEq (functerm f xs) (functerm g ys) with funcEq f g
...                                    | no  neq = no φ
                                                   where φ : _
                                                         φ refl = neq refl
...                                    | yes refl with vecEq termEq xs ys
...                                               | yes refl = yes refl
...                                               | no  neq = no φ
                                                              where φ : _
                                                                    φ refl = neq refl

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
