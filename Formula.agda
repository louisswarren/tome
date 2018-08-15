module Formula where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String
open import common


-- "Let a countably infinite set {vi | i ∈ N} of variables be given."
record Variable : Set where
  constructor mkvar
  field
    name : String


-- "For every natural number n ≥ 0 a ... set of n-ary relation symbols."
record Relation : Set where
  constructor mkrel
  field
    arity : ℕ
    name  : String

mkprop : String → Relation
mkprop s = mkrel zero s


-- "For every natural number n ≥ 0 a ... set of n-ary function symbols."
record Function : Set where
  constructor mkfunc
  field
    arity : ℕ
    name  : String

mkconst : String → Function
mkconst s = mkfunc zero s


-- "Terms are inductively defined as follows.
--  (i)   Every variable is a term.
--  (ii)  Every constant is a term.
--  (iii) If t1, . . . , tn are terms and f is an n-ary function symbol with
--        n ≥ 1, then f(t1 , . . . , tn ) is a term."

data Term : Set where
  varterm  : Variable → Term
  functerm : (f : Function) → Vec Term (Function.arity f) → Term


-- "If t1, . . . , tn are terms and R is an n-ary relation symbol, then
--  R(t1, . . . , tn ) is a prime formula ... Formulas are inductively defined
--- from prime formulas.
data Formula : Set where
  atom   : (r : Relation) → Vec Term (Relation.arity r) → Formula
  _⇒_    : Formula → Formula → Formula
  _∧_    : Formula → Formula → Formula
  _∨_    : Formula → Formula → Formula
  Λ      : Variable → Formula → Formula
  V      : Variable → Formula → Formula
  _[_/_] : Formula → Term → Term → Formula

infixr 105 _⇒_ _⇔_
infixr 106 _∨_
infixr 107 _∧_

_⇔_ : Formula → Formula → Formula
Φ ⇔ Ψ = (Φ ⇒ Ψ) ∧ (Ψ ⇒ Φ)

⊥ = atom (mkprop "⊥") []

¬ ¬¬ : Formula → Formula
¬ Φ = Φ ⇒ ⊥
¬¬ Φ = ¬(¬ Φ)

--------------------------------------------------------------------------------

data _BoundIn_ : Term → Formula → Set where
  -- Atom constructor recurses
  _⇒_ : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ⇒ β)
  _∧_ : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ∧ β)
  _∨_ : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ∨ β)
  Λ∣  : ∀ x α → (varterm x) BoundIn Λ x α
  V∣  : ∀ x α → (varterm x) BoundIn V x α
  Λ   : ∀{t α} → ∀ x → t BoundIn α → t BoundIn Λ x α
  V   : ∀{t α} → ∀ x → t BoundIn α → t BoundIn V x α
