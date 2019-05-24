--STRIP: \begin{code}

--STRIP: module Formula where

open import Agda.Builtin.Sigma

open import Decidable
open import Nat
open import Vec

--STRIP: \end{code}
--STRIP: 
--STRIP: \subsection{Basic definitions}
--STRIP: 
--STRIP: We adopt the definitions of \citet{schwichtenberg}. In particular, there are
--STRIP: countably many variables, and there are countably many function symbols of each
--STRIP: (natural) airty. Function symbols of different arities with the same index are
--STRIP: considered different.
--STRIP: \begin{code}

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

--STRIP: \end{code}
--STRIP: By defining these as \inline{record} types, we get destructors for accessing
--STRIP: the indices and arities, which we then extract into the current module for ease
--STRIP: of use. Note that the indices are natural numbers. While it seems equivalent
--STRIP: and more useful to index using strings, strings are not supported by Agda's
--STRIP: proof search. Internally, strings are not recursively defined as the natural
--STRIP: numbers are; instead the string type is a postulated type which is bound to
--STRIP: string literals.
--STRIP: 
--STRIP: Terms are either variables, or functions applied to the appropriate number of
--STRIP: arguments (zero for constants).
--STRIP: \begin{code}

data Term : Set where
  varterm  : (x : Variable) → Term
  functerm : (f : Function) → (ts : Vec Term (funcarity f)) → Term

--STRIP: \end{code}
--STRIP: 
--STRIP: Relation symbols work the same way as function symbols.
--STRIP: \begin{code}

record Relation : Set where
  constructor rel
  field
    idx   : ℕ
    arity : ℕ

open Relation renaming (idx to relidx ; arity to relarity)

--STRIP: \end{code}
--STRIP: 
--STRIP: We now define atoms (prime formulae), and the logical connectives, using
--STRIP: $\bigwedge$ and $\bigvee$ in place of $\forall$ and $\exists$, since $\forall$
--STRIP: is reserved by Agda.
--STRIP: \todo{Rename $\Lambda$ and $V$}
--STRIP: \begin{code}

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

data ∣_∣≡_ : Formula → ℕ → Set where
  atom   : (r : Relation) → (ts : Vec Term (relarity r)) → ∣ atom r ts ∣≡ 0
  _⇒_    : ∀{α β} → ∀ n m → ∣ α ∣≡ n → ∣ β ∣≡ m → ∣ α ⇒ β ∣≡ suc (m + n)
  _∧_    : ∀{α β} → ∀ n m → ∣ α ∣≡ n → ∣ β ∣≡ m → ∣ α ∧ β ∣≡ suc (m + n)
  _∨_    : ∀{α β} → ∀ n m → ∣ α ∣≡ n → ∣ β ∣≡ m → ∣ α ∨ β ∣≡ suc (m + n)
  Λ      : ∀{α x} → ∀ n → ∣ α ∣≡ n → ∣ Λ x α ∣≡ suc n
  V      : ∀{α x} → ∀ n → ∣ α ∣≡ n → ∣ V x α ∣≡ suc n

postulate ∣_∣ : Formula → ℕ
postulate ∣_∣pf : ∀ α → ∣ α ∣≡ ∣ α ∣

--STRIP: \end{code}
--STRIP: 
--STRIP: Equality of formulae is decidable. Logically, this follows from the fact that
--STRIP: formulae are inductively defined. The proof is obtained by case analysis, using
--STRIP: lemata on the types used to construct formulae. As these proofs are
--STRIP: unremarkable, and follow the same pattern as the proof for decidable equality
--STRIP: of natural numbers above, they are omitted from the latex-typeset form of this
--STRIP: file.
--STRIP: \begin{code}

varEq : Decidable≡ Variable
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

varEq (var n) (var m) with natEq n m
...                   | yes refl = yes refl
...                   | no  n≢m  = no λ { refl → n≢m refl }

--STRIP: \end{code}
--STRIP: }
--STRIP: \begin{code}

relEq : Decidable≡ Relation
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

relEq (rel n j) (rel m k) with natEq n m
...                       | no  n≢m  = no λ { refl → n≢m refl }
...                       | yes refl with natEq j k
...                                  | yes refl = yes refl
...                                  | no  j≢k  = no λ { refl → j≢k refl }

--STRIP: \end{code}
--STRIP: }
--STRIP: \begin{code}

funcEq : Decidable≡ Function
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

funcEq (func n j) (func m k) with natEq n m
...                          | no  n≢m  = no λ { refl → n≢m refl }
...                          | yes refl with natEq j k
...                                     | yes refl = yes refl
...                                     | no  j≢k  = no λ { refl → j≢k refl }

--STRIP: \end{code}
--STRIP: }
--STRIP: \begin{code}

vecEq : ∀{n} {A : Set} → Decidable≡ A → Decidable≡ (Vec A n)
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

vecEq eq [] [] = yes refl
vecEq eq (x ∷ xs) (y ∷ ys) with eq x y
...                        | no  x≢y  = no λ { refl → x≢y refl }
...                        | yes refl with vecEq eq xs ys
...                                   | yes refl  = yes refl
...                                   | no  xs≢xy = no λ { refl → xs≢xy refl }

--STRIP: \end{code}
--STRIP: }
--STRIP: \begin{code}

termEq : Decidable≡ Term
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

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

--STRIP: \end{code}
--STRIP: }
--STRIP: \begin{code}

formulaEq : Decidable≡ Formula
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

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

--STRIP: \end{code}
--STRIP: }
--STRIP: 
--STRIP: \subsection{Variable freedom}
--STRIP: 
--STRIP: We define the conditions for a variable to be \emph{not free} in a formula.
--STRIP: Instead of first defining \emph{free} and then taking \emph{not free} to be the
--STRIP: negation, we use a positive definition, since later definitions only ever
--STRIP: require proof that a variable is not free. For a given term $t$, $x$ is not
--STRIP: free in $t$ if $t$ is a variable other than $x$. Otherwise if the term is a
--STRIP: function on arguments $ts$, then $x$ is not free if it is not free anywhere in
--STRIP: $ts$, which can be checked by applying \inline{All} to this definition.
--STRIP: Separating the declaration and definition of \inline{_NotInTerm_} allows it to
--STRIP: be defined mutually with the case for a vector of terms.
--STRIP: \begin{code}

data _NotInTerm_ (x : Variable) : Term → Set

_NotInTerms_ : ∀{n} → Variable → Vec Term n → Set
x NotInTerms ts = All (x NotInTerm_) ts

data _NotInTerm_ x where
  varterm  : ∀{y} → x ≢ y → x NotInTerm (varterm y)
  functerm : ∀{f} {us : Vec Term (funcarity f)}
               → x NotInTerms us → x NotInTerm (functerm f us)

--STRIP: \end{code}
--STRIP: 
--STRIP: A variable is shown to be not free in a formula with the obvious recursive
--STRIP: definition. It is not free inside a quantification over a subformula $\alpha$
--STRIP: either if it is the quantification variable, or else if it is not free in
--STRIP: $\alpha$.  Separate constructors are given for these. A variable is not free
--STRIP: inside an atom if it is not free within that atom, meaning it is not free in
--STRIP: the terms that the relation is operating on.
--STRIP: \todo{Notation: \inline{Λ∣}?}
--STRIP: \begin{code}

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

--STRIP: \end{code}
--STRIP: 
--STRIP: Variable freedom within a vector of terms is decidable, simply by searching
--STRIP: through the vector for occurences.
--STRIP: \begin{code}

_notInTerms_ : ∀{n} → ∀ x → (ts : Vec Term n) → Dec (x NotInTerms ts)
x notInTerms [] = yes []
--STRIP: \end{code}
--STRIP: To check against a variable term, use the decidable equality of variables.
--STRIP: \begin{code}
x notInTerms (varterm y ∷ ts) with varEq x y
...    | yes refl = no λ { (varterm x≢x ∷ _) → x≢x refl }
...    | no  x≢y  with x notInTerms ts
...               | yes x∉ts = yes (varterm x≢y ∷ x∉ts)
...               | no ¬x∉ts = no λ { (_ ∷ x∉ts) → ¬x∉ts x∉ts }
--STRIP: \end{code}
--STRIP: To check against a function term, recurse over the arguments.
--STRIP: \begin{code}
x notInTerms (functerm f us ∷ ts) with x notInTerms us
...    | no ¬x∉us = no λ { (functerm x∉us ∷ _) → ¬x∉us x∉us }
...    | yes x∉us with x notInTerms ts
...               | yes x∉ts = yes (functerm x∉us ∷ x∉ts)
...               | no ¬x∉ts = no λ { (_ ∷ x∉ts) → ¬x∉ts x∉ts }

--STRIP: \end{code}
--STRIP: Note that each case must check if $x$ is free in the remaining terms in the
--STRIP: vector. A shorter proof would do this check at the same time as doing a case
--STRIP: split on the first term, as was done for variable substitution in a vector of
--STRIP: terms above. However, if a term for which $x$ is free is found, it is not
--STRIP: necessary to continue recursing through the vector, so it is better
--STRIP: computationally not to do so.
--STRIP: 
--STRIP: The same logic can be used for a single term, calling the above function to
--STRIP: check function arguments. The proposition \inline{_NotInTerms_} is defined
--STRIP: using \inline{All} and \inline{_NotInTerm_}, so it is tempting to try to first
--STRIP: prove that the single term case is decidable, and then generalise to vectors
--STRIP: using the lemma that \inline{All} is decidable for decidable predicates.
--STRIP: However, this would not be structurally recursive, and so Agda would not see
--STRIP: this as terminating. Above, the case \mintinline{agda}{x notInTerms t ∷ ts}
--STRIP: depends on the result of \inline{x notFreeInterms ts}, which is in fact
--STRIP: primitively recursive. However, if it instead depended on the result of
--STRIP: \inline{all (x notInTerm_) ts}, Agda cannot determine that \inline{x
--STRIP: notInTerm_} will be applied only to arguments structurally smaller than
--STRIP: \inline{t ∷ ts}.
--STRIP: \begin{code}

_notInTerm_ : (x : Variable) → (t : Term) → Dec (x NotInTerm t)
x notInTerm varterm y     with varEq x y
...                       | yes refl = no λ { (varterm x≢x) → x≢x refl }
...                       | no x≢y  = yes (varterm x≢y)
x notInTerm functerm f ts with x notInTerms ts
...                       | yes x∉ts = yes (functerm x∉ts)
...                       | no ¬x∉ts = no λ { (functerm x∉ts) → ¬x∉ts x∉ts }

--STRIP: \end{code}
--STRIP: 
--STRIP: Now for formulae, to determine if a variable is not free, we apply the above
--STRIP: for atoms, check recursively for the logical connectives, and check if the
--STRIP: variable is the quantifying variable for the quantifiers.
--STRIP: \begin{code}

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

--STRIP: \end{code}
--STRIP: 
--STRIP: 
--STRIP: \subsection{Substitutions}
--STRIP: 
--STRIP: We define what it means for a formula $\beta$ to be obtained from $\alpha$ by
--STRIP: replacing all instances of a variable $x$ with term $t$.  The definitions have
--STRIP: a similar structure to that of \inline{_NotFreeIn_} above. Note that the more
--STRIP: general case of replacing terms with terms is not needed for natural deduction.
--STRIP: 
--STRIP: Inside a vector of terms, wherever $x$ occurs, it is replaced with $t$. Any
--STRIP: variable distinct from $x$ is left unchanged. For a function application, $x$
--STRIP: is replaced with $t$ inside all of the arguments.
--STRIP: \begin{code}

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

--STRIP: \end{code}
--STRIP: 
--STRIP: The definition for formulae follows.
--STRIP: \begin{code}

data _[_/_]≡_ : Formula → Variable → Term → Formula → Set where
--STRIP: \end{code}
--STRIP: The \inline{ident} constructor gives the case that replacing $x$ with $x$
--STRIP: yields the original formula. While this is actually a derived rule, in practice
--STRIP: it is the case we usually want to use. Providing a constructor allows Agda's
--STRIP: proof search to solve this case easily.
--STRIP: \begin{code}
  ident : ∀ α x → α [ x / varterm x ]≡ α
--STRIP: \end{code}
--STRIP: If $x$ is in fact not free in $\alpha$, then replacing it with any term should
--STRIP: leave $\alpha$ unchanged. This rule is not derivable when $t$ is not free for
--STRIP: $x$ in $\alpha$. For example, without this constructor it would not be possible
--STRIP: to prove that $(\forall y A)[x/y]\equiv A$, where $A$ is a propositional
--STRIP: \todo{nullary predicate} formula.
--STRIP: \begin{code}
  notfree : ∀{α x t} → x NotFreeIn α → α [ x / t ]≡ α
--STRIP: \end{code}
--STRIP: The propositional cases are similar to those of the \inline{_NotFreeIn_} type
--STRIP: above.
--STRIP: \begin{code}
  atom    : ∀{x t}
              → (r : Relation) → {xs ys : Vec Term (relarity r)}
              → [ xs ][ x / t ]≡ ys → (atom r xs) [ x / t ]≡ (atom r ys)
  _⇒_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ⇒ β) [ x / t ]≡ (α′ ⇒ β′)
  _∧_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∧ β) [ x / t ]≡ (α′ ∧ β′)
  _∨_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∨ β) [ x / t ]≡ (α′ ∨ β′)
--STRIP: \end{code}
--STRIP: Variable substitution for a quantified formula has two cases, which are similar
--STRIP: to their counterparts in \inline{_NotFreeIn_}. If $x$ is the quantification
--STRIP: variable, then the formula is unchanged.
--STRIP: \begin{code}
  Λ∣      : ∀{t} → (x : Variable) → (α : Formula) → (Λ x α) [ x / t ]≡ (Λ x α)
  V∣      : ∀{t} → (x : Variable) → (α : Formula) → (V x α) [ x / t ]≡ (V x α)
--STRIP: \end{code}
--STRIP: If $x$ is not the quantification variable and $t$ is free for $x$ in in the
--STRIP: formula ($x$ is not free in term $t$), then the substitution simply occurs
--STRIP: inside the quantification.
--STRIP: \begin{code}
  Λ       : ∀{α β x y t} → x ≢ y → y NotInTerm t
              → α [ x / t ]≡ β → (Λ y α) [ x / t ]≡ (Λ y β)
  V       : ∀{α β x y t} → x ≢ y → y NotInTerm t
              → α [ x / t ]≡ β → (V y α) [ x / t ]≡ (V y β)

--STRIP: \end{code}
--STRIP: 
--STRIP: Given $\alpha$, $x$, $t$, the $\beta$ satisfying $\alpha[x/t]\equiv \beta$
--STRIP: should be unique, so that variable substitution is functional. This can first
--STRIP: be shown for the special cases \inline{ident} and \inline{notfree}, by
--STRIP: recursing through the constructors down to the atomic case, and recursing
--STRIP: through the term substitutions down to the variable terms. The proofs simply
--STRIP: have \inline{refl} on the right side of every line, and are omitted. Their
--STRIP: structures are very similar to the next two proofs.
--STRIP: \begin{code}

subIdentFunc : ∀{α x β} → α [ x / varterm x ]≡ β → α ≡ β
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

subIdentFunc (ident α x) = refl
subIdentFunc (notfree x) = refl
subIdentFunc (atom r ts) = vecEq→Eq (termsLemma ts)
  where
    vecEq→Eq : {us vs : Vec Term (relarity r)} → us ≡ vs → atom r us ≡ atom r vs
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

--STRIP: \end{code}
--STRIP: }
--STRIP: \begin{code}
subNotFreeFunc : ∀{α x t β} → α [ x / t ]≡ β → x NotFreeIn α → α ≡ β
-- Proof omitted.

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

subNotFreeFunc (ident α x) x∉α = refl
subNotFreeFunc (notfree x) x∉α = refl
subNotFreeFunc (atom p r) (atom x∉xs) = vecEq→Eq (termsLemma r x∉xs)
  where
    vecEq→Eq : {us vs : Vec Term (relarity p)} → us ≡ vs → atom p us ≡ atom p vs
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

--STRIP: \end{code}
--STRIP: }
--STRIP: 
--STRIP: Variable substitution inside a vector of terms is functional.
--STRIP: \begin{code}

subTermsFunc : ∀{n x t} {us vs ws : Vec Term n}
               → [ us ][ x / t ]≡ vs → [ us ][ x / t ]≡ ws → vs ≡ ws
subTermsFunc [] [] = refl
--STRIP: \end{code}
--STRIP: First recurse over the rest of the two vectors.
--STRIP: \begin{code}
subTermsFunc (s ∷ ss) (r ∷ rs) with subTermsFunc ss rs
--STRIP: \end{code}
--STRIP: It is possible to pattern match inside the \inline{with} block to examine the
--STRIP: two substitutions made for the heads of the vectors. In the case that the first
--STRIP: term is substituted using \inline{varterm≡} in each case, the resulting vectors
--STRIP: must both have $x$ at the head, so the proof is \inline{refl}.
--STRIP: \begin{code}
subTermsFunc (varterm≡     ∷ _) (varterm≡     ∷ _) | refl = refl
--STRIP: \end{code}
--STRIP: It would be contradictory for the first term in $us$ to both match and differ
--STRIP: from $x$.
--STRIP: \begin{code}
subTermsFunc (varterm≡     ∷ _) (varterm≢ x≢x ∷ _) | refl = ⊥-elim (x≢x refl)
subTermsFunc (varterm≢ x≢x ∷ _) (varterm≡     ∷ _) | refl = ⊥-elim (x≢x refl)
--STRIP: \end{code}
--STRIP: If the head of $us$ is a variable different from $x$, then it is unchanged in
--STRIP: each case, so the proof is \inline{refl}.
--STRIP: \begin{code}
subTermsFunc (varterm≢ x≢y ∷ _) (varterm≢ _   ∷ _) | refl = refl
--STRIP: \end{code}
--STRIP: Finally, in the case of a function, recurse over the vector of arguments.
--STRIP: \todo{explain rewrite}
--STRIP: \begin{code}
subTermsFunc (functerm st  ∷ _) (functerm rt  ∷ _)
             | refl rewrite subTermsFunc st rt = refl

--STRIP: \end{code}
--STRIP: 
--STRIP: Now, show variable substitution is functional.
--STRIP: \begin{code}

subFunc : ∀{x t α β γ} → α [ x / t ]≡ β → α [ x / t ]≡ γ → β ≡ γ
--STRIP: \end{code}
--STRIP: If either substitution came from \inline{ident} or \inline{notfree}, invoke one
--STRIP: of the above lemata. Note that if they occured in the right substitution, the
--STRIP: lemata prove $\gamma \equiv \beta$, so \inline{rewrite} is used to recover
--STRIP: $\beta \equiv \gamma$.
--STRIP: \begin{code}
subFunc (ident α x)   r             = subIdentFunc r
subFunc (notfree x∉α) r             = subNotFreeFunc r x∉α
subFunc r             (ident α x)   rewrite subIdentFunc r       = refl
subFunc r             (notfree x∉α) rewrite subNotFreeFunc r x∉α = refl
--STRIP: \end{code}
--STRIP: The atomic case comes from the above lemma.
--STRIP: \begin{code}
subFunc (atom p s)    (atom .p r)   rewrite subTermsFunc s r = refl
--STRIP: \end{code}
--STRIP: The propositional connectives can be proved inductively.
--STRIP: \begin{code}
subFunc (s₁ ⇒ s₂)     (r₁ ⇒ r₂)     with subFunc s₁ r₁ | subFunc s₂ r₂
...                                 | refl | refl = refl
subFunc (s₁ ∧ s₂)     (r₁ ∧ r₂)     with subFunc s₁ r₁ | subFunc s₂ r₂
...                                 | refl | refl = refl
subFunc (s₁ ∨ s₂)     (r₁ ∨ r₂)     with subFunc s₁ r₁ | subFunc s₂ r₂
...                                 | refl | refl = refl
--STRIP: \end{code}
--STRIP: If the formula is a quantification over $x$, then neither substitution changes
--STRIP: the formula.
--STRIP: \begin{code}
subFunc (Λ∣ x α)      (Λ∣ .x .α)    = refl
subFunc (V∣ x α)      (V∣ .x .α)    = refl
--STRIP: \end{code}
--STRIP: It is contradictory for one substitution to occur by matching $x$
--STRIP: with the quantifier, and the other to have a different quantifier.
--STRIP: \begin{code}
subFunc (Λ∣ x α)      (Λ x≢x _ r)   = ⊥-elim (x≢x refl)
subFunc (V∣ x α)      (V x≢x _ r)   = ⊥-elim (x≢x refl)
subFunc (Λ x≢x _ s)   (Λ∣ x α)      = ⊥-elim (x≢x refl)
subFunc (V x≢x _ s)   (V∣ x α)      = ⊥-elim (x≢x refl)
--STRIP: \end{code}
--STRIP: Finally, if the formula is a quantification over a variable other than $x$,
--STRIP: then substitution occurs inside the quantified formula, so recurse inside those
--STRIP: substitutions.
--STRIP: \begin{code}
subFunc (Λ _ _ s)     (Λ _ _ r)     rewrite subFunc s r = refl
subFunc (V _ _ s)     (V _ _ r)     rewrite subFunc s r = refl

--STRIP: \end{code}
--STRIP: 
--STRIP: 
--STRIP: Substitutions do not always exist. For example, there is no way of constructing
--STRIP: a formula for $(\forall y P x)[x/y]$. In general, $\alpha [x/t]$ exists only if
--STRIP: $t$ is \emph{free for} $x$ \emph{in} $\alpha$, meaning no variables in $t$
--STRIP: would become bound inside $\alpha$. This can be formalised by using (with minor
--STRIP: modification) the rules of \cite{vandalen}.
--STRIP: \begin{code}

data _FreeFor_In_ (t : Term) (x : Variable) : Formula → Set where
  notfree : ∀{α} → x NotFreeIn α → t FreeFor x In α
  atom    : ∀ r us → t FreeFor x In atom r us
  _⇒_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ⇒ β
  _∧_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ∧ β
  _∨_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ∨ β
  Λ∣      : ∀ α → t FreeFor x In Λ x α
  V∣      : ∀ α → t FreeFor x In V x α
  Λ       : ∀{α y} → y NotInTerm t → t FreeFor x In α → t FreeFor x In Λ y α
  V       : ∀{α y} → y NotInTerm t → t FreeFor x In α → t FreeFor x In V y α

--STRIP: \end{code}
--STRIP: 
--STRIP: The definitions above for variable substitution lead directly to a procedure
--STRIP: for computing substitutions. Given $\alpha$, $x$, $t$, and a proof that $t$ is
--STRIP: free for $x$ in $\alpha$, we compute a $\beta$ and a proof that
--STRIP: $\alpha[x/t] \equiv \beta$. The sigma (dependent sum) type can be used to
--STRIP: encapsulate both a value and a proof regarding that value.
--STRIP: 
--STRIP: \todo{recurse or recur?}
--STRIP: First for vectors of terms, recurse through all function arguments, and replace
--STRIP: any variables equal to $x$ with $t$. In the code below, we do a case split on
--STRIP: the first term, and use a \inline{with} block to get the substitution for the
--STRIP: rest of the vector simultaneously, since this substitution is required in
--STRIP: either case.
--STRIP: \begin{code}

[_][_/_] : ∀{n} → (us : Vec Term n) → ∀ x t → Σ (Vec Term n) [ us ][ x / t ]≡_
[ [] ][ x / t ] = [] , []
[ u ∷ us ][ x / t ] with [ us ][ x / t ]
[ varterm y     ∷ us ][ x / t ] | vs , vspf with varEq x y
...    | yes refl = (t         ∷ vs) , (varterm≡     ∷ vspf)
...    | no  x≢y  = (varterm y ∷ vs) , (varterm≢ x≢y ∷ vspf)
[ functerm f ws ∷ us ][ x / t ] | vs , vspf with [ ws ][ x / t ]
...    | xs , xspf = (functerm f xs ∷ vs) , (functerm xspf ∷ vspf)

--STRIP: \end{code}
--STRIP: 
--STRIP: For formulae, a proof that $t$ is free for $x$ in the formula must be supplied.
--STRIP: The term $t$ is fixed by supplying such a proof, so for convenience of
--STRIP: notation, the proof is supplied in place of the term. In the following code we
--STRIP: will use names like \inline{x∉α} to denote proofs of `$x$ is not free in
--STRIP: $\alpha$`.
--STRIP: \begin{code}

_[_/_] : ∀{t} → ∀ α x → t FreeFor x In α → Σ Formula (α [ x / t ]≡_)
α [ x / notfree ¬x∉α ]       = α , notfree ¬x∉α
--STRIP: \end{code}
--STRIP: For atomic formulae, apply the above lemma.
--STRIP: \begin{code}
_[_/_] {t} (atom r ts) x tff with [ ts ][ x / t ]
...                          | ts′ , tspf = atom r ts′ , atom r tspf
--STRIP: \end{code}
--STRIP: For the propositional connectives, the substitution is obtained recursively.
--STRIP: \begin{code}
(α ⇒ β) [ x / tffα ⇒ tffβ ]  with α [ x / tffα ] | β [ x / tffβ ]
...                          | α′ , αpf | β′ , βpf = α′ ⇒ β′ , αpf ⇒ βpf
(α ∧ β) [ x / tffα ∧ tffβ ]  with α [ x / tffα ] | β [ x / tffβ ]
...                          | α′ , αpf | β′ , βpf = α′ ∧ β′ , αpf ∧ βpf
(α ∨ β) [ x / tffα ∨ tffβ ]  with α [ x / tffα ] | β [ x / tffβ ]
...                          | α′ , αpf | β′ , βpf = α′ ∨ β′ , αpf ∨ βpf
--STRIP: \end{code}
--STRIP: For generalisation, check if $x$ is the quantifier, and if so do nothing.
--STRIP: Otherwise, recurse.
--STRIP: \begin{code}
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

--STRIP: \end{code}
--STRIP: 
--STRIP: We have proved that if $t$ is free for $x$ in $α$ then $α[x/t]$ exists. The
--STRIP: converse is also true, meaning that \inline{_FreeFor_In_} precisely captures
--STRIP: the notion of a substitution being possible.
--STRIP: \begin{code}

subFreeFor : ∀{α x t β} → α [ x / t ]≡ β → t FreeFor x In α
-- Proof omitted.

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

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

--STRIP: \end{code}
--STRIP: }
--STRIP: 
--STRIP: If a variable has been substituted by a term not involving that variable, then
--STRIP: the variable is not free in the resulting term.
--STRIP: \begin{code}

subNotFree : ∀{α x t β} → x NotInTerm t → α [ x / t ]≡ β → x NotFreeIn β
subNotFree (varterm x≢x) (ident α x) = ⊥-elim (x≢x refl)
subNotFree x∉t (notfree x∉α)   = x∉α
subNotFree x∉t (atom r p)       = atom (termsLemma x∉t p)
  where
    termsLemma : ∀{n x t} {us vs : Vec Term n} → x NotInTerm t
                      → [ us ][ x / t ]≡ vs → x NotInTerms vs
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


--STRIP: \end{code}
--STRIP: 
--STRIP: 
--STRIP: \begin{code}

subInverse : ∀{ω α x β}
             → ω NotFreeIn α → α [ x / varterm ω ]≡ β → β [ ω / varterm x ]≡ α
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


--STRIP: \end{code}
--STRIP: 
--STRIP: \subsection{Fresh variables}
--STRIP: 
--STRIP: A variable is \emph{fresh} if appears nowhere (free or bound) in a formula.
--STRIP: \begin{code}

data _FreshIn_ (x : Variable) : Formula → Set where
  atom : ∀{r ts} → x NotInTerms ts  → x FreshIn (atom r ts)
  _⇒_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ⇒ β
  _∧_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ∧ β
  _∨_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ∨ β
  Λ    : ∀{α y} → y ≢ x → x FreshIn α → x FreshIn Λ y α
  V    : ∀{α y} → y ≢ x → x FreshIn α → x FreshIn V y α

--STRIP: \end{code}
--STRIP: 
--STRIP: Certainly, if a variable is fresh in a formula, then it is also not free, and
--STRIP: every term is free for that variable. The proofs are trivial, and are omitted.
--STRIP: \begin{code}

freshNotFree : ∀{α x} → x FreshIn α → x NotFreeIn α
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

freshNotFree (atom x∉ts)   = atom x∉ts
freshNotFree (xfrα ⇒ xfrβ) = freshNotFree xfrα ⇒ freshNotFree xfrβ
freshNotFree (xfrα ∧ xfrβ) = freshNotFree xfrα ∧ freshNotFree xfrβ
freshNotFree (xfrα ∨ xfrβ) = freshNotFree xfrα ∨ freshNotFree xfrβ
freshNotFree (Λ _ xfrα)    = Λ _ (freshNotFree xfrα)
freshNotFree (V _ xfrα)    = V _ (freshNotFree xfrα)

--STRIP: \end{code}
--STRIP: }
--STRIP: \begin{code}

freshFreeFor : ∀{α x} → x FreshIn α → ∀ y → (varterm x) FreeFor y In α
-- Proof omitted

--STRIP: \end{code}
--STRIP: \AgdaHide{
--STRIP: \begin{code}

freshFreeFor (atom _)      y = atom _ _
freshFreeFor (xfrα ⇒ xfrβ) y = freshFreeFor xfrα y ⇒ freshFreeFor xfrβ y
freshFreeFor (xfrα ∧ xfrβ) y = freshFreeFor xfrα y ∧ freshFreeFor xfrβ y
freshFreeFor (xfrα ∨ xfrβ) y = freshFreeFor xfrα y ∨ freshFreeFor xfrβ y
freshFreeFor (Λ x≢y xfrα)  y = Λ (varterm x≢y) (freshFreeFor xfrα y)
freshFreeFor (V x≢y xfrα)  y = V (varterm x≢y) (freshFreeFor xfrα y)

--STRIP: \end{code}
--STRIP: }
--STRIP: 
--STRIP: For the purposes of variable substitution, we need a way
--STRIP: \todo{why?}
--STRIP: to generate a fresh
--STRIP: variable for a given formula. Only finitely many variables occur in a given
--STRIP: term or formula, so there is a greatest (with respect to the natural number
--STRIP: indexing) variable occuring in each term or formula; all variables greater than
--STRIP: this are fresh. This means that the least fresh variable will not be found. For
--STRIP: example, for $P x_0 \lor P x_2$, we find that $x_3, x_4, \dotsc$ are fresh,
--STRIP: missing $x_1$. However, finding the least fresh variable cannot be done
--STRIP: recursively. Consider $\alpha = (P x_0 \lor P x_2) \land P x_1$; we find $x_1$
--STRIP: is fresh to the left of the conjunctive, and $x_0$ is fresh to the right, but
--STRIP: this does not indicate that $x_2$ will not be fresh in $\alpha$.
--STRIP: 
--STRIP: The built-in sigma type has been imported. A simplified version of its
--STRIP: definition is commented below.
--STRIP: \begin{code}


--STRIP: \end{code}
--STRIP: \inline{Σ A B} can be proved by providing an $x$ of type $A$, and a proof of $B
--STRIP: x$. The sigma type then can be used to define existential propositions.
--STRIP: 
--STRIP: We first compute the greatest variable occuring in a vector of terms, and then
--STRIP: specialise to a single term, for termination reasons similar to that of
--STRIP: \inline{_notInTerms_}. For terms, there is no distinction between being fresh
--STRIP: and being not-free.
--STRIP: \begin{code}

supFreeTerms : ∀{k} → (ts : Vec Term k)
               → Σ ℕ (λ ⌈ts⌉ → ∀ n → ⌈ts⌉ < n → var n NotInTerms ts)
supFreeTerms [] = zero , λ _ _ → []
--STRIP: \end{code}
--STRIP: If the first term is a variable, check if its index is greater than the
--STRIP: greatest \todo{supremum} free variable of the rest of the terms. If not, use the
--STRIP: variable from the rest of the terms.
--STRIP: \begin{code}
supFreeTerms (varterm (var m) ∷ ts) with supFreeTerms ts
... | ⌈ts⌉ , tspf with ≤total m ⌈ts⌉
...               | less m≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    orderneq : ∀{n m} → n < m → var m ≢ var n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n
                    → All (var n NotInTerm_) (varterm (var m) ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = varterm (orderneq (≤trans (sn≤sm m≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
--STRIP: \end{code}
--STRIP: Otherwise, use this variable.
--STRIP: \begin{code}
...               | more ⌈ts⌉≤m = m , notFreeIsm
  where
    orderneq : ∀{n m} → n < m → var m ≢ var n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIsm : ∀ n → m < n → All (var n NotInTerm_) (varterm (var m) ∷ ts)
    notFreeIsm n m<n = varterm (orderneq m<n)
                       ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤m) m<n)
--STRIP: \end{code}
--STRIP: If the first term is a function, then check if the greatest free variable in
--STRIP: its arguments is greater than the greatest free variable of the rest of the
--STRIP: terms. If not, use the variable from the rest of the terms.
--STRIP: \begin{code}
supFreeTerms (functerm f us     ∷ ts) with supFreeTerms us | supFreeTerms ts
... | ⌈us⌉ , uspf | ⌈ts⌉ , tspf with ≤total ⌈us⌉ ⌈ts⌉
...                             | less ⌈us⌉≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n → All (var n NotInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = functerm (uspf n (≤trans (sn≤sm ⌈us⌉≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
--STRIP: \end{code}
--STRIP: Otherwise, use the variable from the function's arguments.
--STRIP: \begin{code}
...                             | more ⌈ts⌉≤⌈us⌉ = ⌈us⌉ , notFreeIs⌈us⌉
  where
    notFreeIs⌈us⌉ : ∀ n → ⌈us⌉ < n → All (var n NotInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈us⌉ n ⌈us⌉<n = functerm (uspf n ⌈us⌉<n)
                             ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤⌈us⌉) ⌈us⌉<n)

--STRIP: \end{code}
--STRIP: 
--STRIP: \todo{minFresh isn't actually a minimum}
--STRIP: Given a formula, we can now produce a variable which is fresh, and for which
--STRIP: all greater variables are fresh.
--STRIP: \begin{code}
minFresh : ∀ α → Σ Variable λ ⌈α⌉ → ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn α
--STRIP: \end{code}
--STRIP: In the atomic case, apply the above lemma to find the largest variable
--STRIP: occuring, and construct the succeeding variable.
--STRIP: \begin{code}
minFresh (atom r ts) with supFreeTerms ts
minFresh (atom r ts) | ⌈ts⌉ , tspf = var (suc ⌈ts⌉)
                                     , (λ n ⌈ts⌉≤n → atom (tspf n ⌈ts⌉≤n))
--STRIP: \end{code}
--STRIP: If all variables greater than or equal to $\lceil\alpha\rceil$ are fresh in
--STRIP: $\alpha$, greater than or equal to $\lceil\beta\rceil$ are fresh in $\beta$,
--STRIP: then any variable greater than or equal to $\max\{\lceil\alpha\rceil,
--STRIP: \lceil\alpha\rceil\}$ will be not free in $\alpha \rightarrow \beta$.
--STRIP: \begin{code}
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
--STRIP: \end{code}
--STRIP: The same reasoning applies to conjunction,
--STRIP: \begin{code}
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
--STRIP: \end{code}
--STRIP: and disjunction.
--STRIP: \begin{code}
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
--STRIP: \end{code}
--STRIP: For a universal generalisation $\forall x \alpha$, take  thre greater of
--STRIP: $\lceil\alpha\rceil$ and the successor of $x$.
--STRIP: \begin{code}
minFresh (Λ x@(var k) α) with minFresh α
...                      | ⌈α⌉ , αpf with ≤total (suc k) (varidx ⌈α⌉)
...                                  | less sk≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var m ≢ var n
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn Λ x α
    freshIs⌈α⌉ n ⌈α⌉≤n = Λ (skNewLemma (≤trans sk≤⌈α⌉ ⌈α⌉≤n)) (αpf n ⌈α⌉≤n)
...                                  | more ⌈α⌉≤sk = var (suc k) , freshIssk
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var m ≢ var n
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIssk : ∀ n → suc k ≤ n → var n FreshIn Λ x α
    freshIssk n sk≤n = Λ (skNewLemma sk≤n) (αpf n (≤trans ⌈α⌉≤sk sk≤n))
--STRIP: \end{code}
--STRIP: The same applies for existential generalisation.
--STRIP: \begin{code}
minFresh (V x@(var k) α) with minFresh α
...                      | ⌈α⌉ , αpf with ≤total (suc k) (varidx ⌈α⌉)
...                                  | less sk≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var m ≢ var n
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn V x α
    freshIs⌈α⌉ n ⌈α⌉≤n = V (skNewLemma (≤trans sk≤⌈α⌉ ⌈α⌉≤n)) (αpf n ⌈α⌉≤n)
...                                    | more ⌈α⌉≤sk = var (suc k) , freshIssk
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var m ≢ var n
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIssk : ∀ n → suc k ≤ n → var n FreshIn V x α
    freshIssk n sk≤n = V (skNewLemma sk≤n) (αpf n (≤trans ⌈α⌉≤sk sk≤n))

--STRIP: \end{code}
--STRIP: 
--STRIP: Finally, a fresh variable can be extracted by choosing the first fresh variable
--STRIP: given by the proof above.
--STRIP: \begin{code}
fresh : ∀ α → Σ Variable (_FreshIn α)
fresh α with minFresh α
...     | ⌈α⌉ , αpf = ⌈α⌉ , αpf (varidx ⌈α⌉) ≤refl

--STRIP: \end{code}
--STRIP: 
--STRIP: \subsection{Formula equivalence}
--STRIP: 
--STRIP: Formulae are equivalent if they are equal up to renaming bound variables. Here,
--STRIP: renaming means substituting a variable for another variable which is not free,
--STRIP: so that the meaning of the formula does not change.
--STRIP: \begin{code}

infix 50 _≈_
data _≈_ : Formula → Formula → Set where
  atom : ∀ r ts → atom r ts ≈ atom r ts
  _⇒_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ⇒ β ≈ α′ ⇒ β′
  _∧_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ∧ β ≈ α′ ∧ β′
  _∨_  : ∀{α β α′ β′} → α ≈ α′ → β ≈ β′ → α ∨ β ≈ α′ ∨ β′
  Λ    : ∀{α α′} → ∀ x → α ≈ α′ → Λ x α ≈ Λ x α′
  Λ/   : ∀{α β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β → β ≈ β′ → Λ x α ≈ Λ y β′
  Λ/′  : ∀{α α′ β′ x y} → α ≈ α′ → y NotFreeIn α′ → α′ [ x / varterm y ]≡ β′ → Λ x α ≈ Λ y β′
  V    : ∀{α α′} → ∀ x → α ≈ α′ → V x α ≈ V x α′
  V/   : ∀{α β β′ x y} → y NotFreeIn α → α [ x / varterm y ]≡ β → β ≈ β′ → V x α ≈ V y β′
  V/′  : ∀{α α′ β′ x y} → α ≈ α′ → y NotFreeIn α′ → α′ [ x / varterm y ]≡ β′ → V x α ≈ V y β′

--STRIP: \end{code}
--STRIP: 
--STRIP: It is important that this relation is symmetric
--STRIP: \begin{code}

≈refl : ∀{α} → α ≈ α
≈refl {atom r ts} = atom r ts
≈refl {α ⇒ β} = ≈refl ⇒ ≈refl
≈refl {α ∧ β} = ≈refl ∧ ≈refl
≈refl {α ∨ β} = ≈refl ∨ ≈refl
≈refl {Λ x α} = Λ x ≈refl
≈refl {V x α} = V x ≈refl


≈sym : ∀{α α′} → α ≈ α′ → α′ ≈ α
≈sym (atom r ts) = atom r ts
≈sym (α≈α′ ⇒ β≈β′) = ≈sym α≈α′ ⇒ ≈sym β≈β′
≈sym (α≈α′ ∧ β≈β′) = ≈sym α≈α′ ∧ ≈sym β≈β′
≈sym (α≈α′ ∨ β≈β′) = ≈sym α≈α′ ∨ ≈sym β≈β′
≈sym (Λ x α≈α′) = Λ x (≈sym α≈α′)
≈sym {Λ x α} {Λ y β′} (Λ/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = Λ x (≈sym β≈β′)
...    | no x≢y = Λ/′ (≈sym β≈β′) (subNotFree (varterm x≢y) α[x/y]≡β) (subInverse y∉α α[x/y]≡β)
≈sym {Λ x α} {Λ y β′} (Λ/′ α≈α′ y∉α′ α′[x/y]≡β′) with varEq x y
...    | yes refl rewrite subIdentFunc α′[x/y]≡β′ = Λ x (≈sym α≈α′)
...    | no  x≢y  = Λ/ (subNotFree (varterm x≢y) α′[x/y]≡β′) (subInverse y∉α′ α′[x/y]≡β′) (≈sym α≈α′)
≈sym (V x α≈α′) = V x (≈sym α≈α′)
≈sym {V x α} {V y β′} (V/ y∉α α[x/y]≡β β≈β′) with varEq x y
...    | yes refl rewrite subIdentFunc α[x/y]≡β = V x (≈sym β≈β′)
...    | no x≢y = V/′ (≈sym β≈β′) (subNotFree (varterm x≢y) α[x/y]≡β) (subInverse y∉α α[x/y]≡β)
≈sym {V x α} {V y β′} (V/′ α≈α′ y∉α′ α′[x/y]≡β′) with varEq x y
...    | yes refl rewrite subIdentFunc α′[x/y]≡β′ = V x (≈sym α≈α′)
...    | no  x≢y  = V/ (subNotFree (varterm x≢y) α′[x/y]≡β′) (subInverse y∉α′ α′[x/y]≡β′) (≈sym α≈α′)


-- todo: capitalisation
notfreeSub : ∀{α β x t z} → z NotFreeIn α → z NotInTerm t → α [ x / t ]≡ β → z NotFreeIn β
notfreeSub z∉α z∉t (ident α x) = z∉α
notfreeSub z∉α z∉t (notfree x∉α) = z∉α
notfreeSub (atom z∉us) z∉t (atom r sub) = atom (termsLemma z∉us z∉t sub)
  where
    termsLemma : ∀{n x t z} {us vs : Vec Term n} → z NotInTerms us
                 → z NotInTerm t → [ us ][ x / t ]≡ vs → z NotInTerms vs
    termsLemma z∉us z∉t [] = z∉us
    termsLemma (z∉u ∷ z∉us) z∉t (varterm≡ ∷ sub) = z∉t ∷ termsLemma z∉us z∉t sub
    termsLemma (z∉u ∷ z∉us) z∉t (varterm≢ x≢y ∷ sub) = z∉u ∷ termsLemma z∉us z∉t sub
    termsLemma (functerm z∉ts ∷ z∉us) z∉t (functerm subts ∷ sub) = functerm (termsLemma z∉ts z∉t subts) ∷ termsLemma z∉us z∉t sub
notfreeSub (z∉α ⇒ z∉β) z∉t (subα ⇒ subβ) = notfreeSub z∉α z∉t subα ⇒ notfreeSub z∉β z∉t subβ
notfreeSub (z∉α ∧ z∉β) z∉t (subα ∧ subβ) = notfreeSub z∉α z∉t subα ∧ notfreeSub z∉β z∉t subβ
notfreeSub (z∉α ∨ z∉β) z∉t (subα ∨ subβ) = notfreeSub z∉α z∉t subα ∨ notfreeSub z∉β z∉t subβ
notfreeSub z∉α z∉t (Λ∣ x α) = z∉α
notfreeSub z∉α z∉t (V∣ x α) = z∉α
notfreeSub (Λ∣ x α) z∉t (Λ x≢y y∉t sub) = Λ∣ x _
notfreeSub (V∣ x α) z∉t (V x≢y y∉t sub) = V∣ x _
notfreeSub (Λ y z∉α) z∉t (Λ x≢y y∉t sub) = Λ y (notfreeSub z∉α z∉t sub)
notfreeSub (V y z∉α) z∉t (V x≢y y∉t sub) = V y (notfreeSub z∉α z∉t sub)


--todo: is it better to split this differently?
≈notfree : ∀{α α′ z} → α ≈ α′ → z NotFreeIn α → z NotFreeIn α′
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

postulate ≈size : ∀{n α α′} → α ≈ α′ → ∣ α′ ∣≡ n → ∣ α ∣≡ n
postulate subSize : ∀{n x t α β} → α [ x / t ]≡ β → ∣ α ∣≡ n → ∣ β ∣≡ n

--STRIP: \end{code}

