The previous modules define the language of natural deduction. This system can
be used to show that certain first-order formulae are derivable in minimal
logic. It is common in logical enquiries to examine proofs regarding axiom
schemes, as we will do later (see also
\citet{hDHabil,troelstra1988constructivism1,troelstra1988constructivism2}).

\AgdaHide{
\begin{code}

module Scheme where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Deduction
open import Formula
open import List
open import Vec

\end{code}
}

We define some metalanguage concepts. A \emph{scheme} is often thought of as a
formula containing schematic variables, which can be replaced by subformulae to
produce a new formula. The following notion is more general than this; instead,
a scheme is just constructed from a function from (a vector of) formulae to a
formula.
\begin{code}

record Scheme : Set where
  constructor scheme
  field
    arity : ℕ
    name  : String
    inst  : Vec Formula arity → Formula

\end{code}
Defining this as a type using a vector, instead of simply using functions,
means that all schemes of all arities are collected under the same type
(\inline{Scheme}), which makes it possible to define a single function for
typesetting scheme proofs later. The definition makes no restriction on the
structure of the instances of the scheme, and is not able to put requirements
on variable freedom.

A scheme is derivable if every instance of the scheme is derivable. A list
$\Omega s$ of schemes is stronger than a scheme $\Phi$ if every instance of
$\Phi$ is derivable from finitely many instances of schemes in $\Omega s$.
Equivalently, $\Omega s$ is stronger than $\Phi$ if the derivability of $\Omega
s$ implies the derivability of $\Phi$.
\begin{code}

Derivable : Scheme → Set₁
Derivable S = ∀ αs → ⊢ (Scheme.inst S αs)

infix 1 _⊃_
_⊃_ : List Scheme → Scheme → Set₁
Ωs ⊃ Φ = (∀ ω → ω List.∈ Ωs → Derivable ω) → Derivable Φ

\end{code}

Because it is nicer to work with $n$-ary functions than unary functions taking
$n$-ary vectors, we define the following notation for creating schemes from
functions,
\begin{code}

nullaryscheme : String → Formula → Scheme
unaryscheme   : String → (Formula → Formula) → Scheme
binaryscheme  : String → (Formula → Formula → Formula) → Scheme

nullaryscheme s f = scheme 0 s λ { [] → f }
unaryscheme   s f = scheme 1 s λ { (α ∷ []) → f α }
binaryscheme  s f = scheme 2 s λ { (α ∷ β ∷ []) → f α β }

\end{code}
expressing derivability for functions,
\begin{code}

infix 1 ⊢₀_ ⊢₁_ ⊢₂_

⊢₀_ : Formula → Set₁
⊢₁_ : (Formula → Formula) → Set₁
⊢₂_ : (Formula → Formula → Formula) → Set₁

⊢₀ s =         ⊢ s
⊢₁ s = ∀ α   → ⊢ s α
⊢₂ s = ∀ α β → ⊢ s α β

\end{code}
and turning derivability of schemes into derivability of functions.
\begin{code}

descheme₀ : {f : Vec Formula 0 → Formula}
            → (∀ αs → ⊢ f αs) → ⊢ f []
descheme₁ : {f : Vec Formula 1 → Formula}
            → (∀ αs → ⊢ f αs) → ∀ α → ⊢ f (α ∷ [])
descheme₂ : {f : Vec Formula 2 → Formula}
            → (∀ αs → ⊢ f αs) → ∀ α β → ⊢ f (α ∷ β ∷ [])

descheme₀ ⊢S     = ⊢S []
descheme₁ ⊢S α   = ⊢S (α ∷ [])
descheme₂ ⊢S α β = ⊢S (α ∷ (β ∷ []))

\end{code}

