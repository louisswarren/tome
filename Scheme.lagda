The previous sections define the language of natural deduction. This system can
be used to show that certain first-order formulae are derivable in minimal
logic. To examine axiom schemes, we define some metalanguage concepts.

\begin{code}

module Scheme where

open import Agda.Builtin.String
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Deduction
open import Formula
open import List
open import Vec

\end{code}

A \emph{scheme} is often thought of as a formula containing schematic
variables, which can be replaced by subformulae to produce a new formula. The
following notion is more general than this; instead, a Scheme is just
constructed from a function from formulae to a formula.

\begin{code}

record Scheme : Set where
  constructor scheme
  field
    arity : ℕ
    inst  : Vec Formula arity → Formula

\end{code}

This definition makes no restriction on the structure of the instances of the
scheme \todo{continuity?}, and is not able to put requirements on variable
freedom.

Because it is nicer to work with $n$-ary functions than unary functions taking
$n$-ary vectors, we define the following constructors for creating schemes from
the former.

\begin{code}

nullaryscheme : Formula → Scheme
nullaryscheme f = scheme 0 λ { [] → f }

unaryscheme : (Formula → Formula) → Scheme
unaryscheme f = scheme 1 λ { (α ∷ []) → f α }

binaryscheme : (Formula → Formula → Formula) → Scheme
binaryscheme f = scheme 2 λ { (α ∷ β ∷ []) → f α β }

\end{code}

Finally, a scheme is derivable if every instance of the scheme is derivable. A
list $\Omega s$ of schemes is stronger than a scheme $\Phi$ if every instance
of $\Phi$ is derivable from finitely many instances of schemes in $\Omega$.
Equivalently, $\Omega s$ is stronger than $\Phi$ if the derivability of $\Omega
s$ implies the derivability of $\Phi$.

\begin{code}

Derivable : Scheme → Set
Derivable S = ∀ αs → ⊢ (Scheme.inst S αs)

infix 1 _⊃_
_⊃_ : List Scheme → Scheme → Set
Ω ⊃ Φ = List.All (Derivable) Ω → Derivable Φ

\end{code}
