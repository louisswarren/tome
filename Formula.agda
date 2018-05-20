module Formula where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
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
  atom : (r : Relation) → Vec Term (Relation.arity r) → Formula
  _⇒_ : Formula → Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  Λ   : Variable → Formula → Formula
  V   : Variable → Formula → Formula

infixr 105 _⇒_ _⇔_
infixr 106 _∨_
infixr 107 _∧_

_⇔_ : Formula → Formula → Formula
Φ ⇔ Ψ = (Φ ⇒ Ψ) ∧ (Ψ ⇒ Φ)

⊥ = atom (mkprop "⊥") []

¬ ¬¬ : Formula → Formula
¬ Φ = Φ ⇒ ⊥
¬¬ Φ = ¬(¬ Φ)



height : Formula → ℕ
height (atom r ts) = zero
height (a ⇒ b)     = suc (maxℕ (height a) (height b))
height (a ∧ b)     = suc (maxℕ (height a) (height b))
height (a ∨ b)     = suc (maxℕ (height a) (height b))
height (Λ x a)     = suc (height a)
height (V x a)     = suc (height a)


--------------------------------------------------------------------------------
-- The above types have an obvious decidable equality coming from string
-- equality. Define an overloaded comparison function, so that extensional
-- equality of formulae is just intensional equality.

data FormulaComponent : Set where
  variable relation function term formula : FormulaComponent

componentType : FormulaComponent → Set
componentType variable = Variable
componentType relation = Relation
componentType function = Function
componentType term     = Term
componentType formula  = Formula


_≈_ : {t : FormulaComponent} → (componentType t) → (componentType t) → Bool

_vec≈_ : ∀{n m} → {t : FormulaComponent}
                → Vec (componentType t) n → Vec (componentType t) m → Bool
_vec≈_ {zero}  {zero}  []       []       = true
_vec≈_ {suc n} {suc m} (x ∷ xs) (y ∷ ys) = (x ≈ y) and (xs vec≈ ys)
_vec≈_ {zero}  {suc m} _        _        = false
_vec≈_ {suc n} {zero}  _        _        = false

_≈_ {variable} (mkvar a)    (mkvar b)    = primStringEquality a b
_≈_ {relation} (mkrel n a)  (mkrel m b)  = n == m and primStringEquality a b
_≈_ {function} (mkfunc n a) (mkfunc m b) = n == m and primStringEquality a b

_≈_ {term} (varterm x)     (varterm y)     = x ≈ y
_≈_ {term} (functerm f xs) (functerm g ys) = (f ≈ g) and (xs vec≈ ys)
_≈_ {term} _               _               = false

_≈_ {formula} (atom r xs) (atom s ys) = (r ≈ s) and (xs vec≈ ys)
_≈_ {formula} (a ⇒ b)     (c ⇒ d)     = (a ≈ c) and (b ≈ d)
_≈_ {formula} (a ∧ b)     (c ∧ d)     = (a ≈ c) and (b ≈ d)
_≈_ {formula} (a ∨ b)     (c ∨ d)     = (a ≈ c) and (b ≈ d)
_≈_ {formula} (V x a)     (V y b)     = (x ≈ y) and (a ≈ b)
_≈_ {formula} (Λ x a)     (Λ y b)     = (x ≈ y) and (a ≈ b)
_≈_ {formula} _           _           = false


--------------------------------------------------------------------------------

{-# TERMINATING #-}
-- Todo: of course this terminates
appearsin : Variable → Term → Bool
appearsin x (varterm y) = x ≈ y
appearsin x (functerm _ ys) = vecany (appearsin x) ys



isfree : Variable → Formula → Bool
isfree x (atom _ ts) = vecany (appearsin x) ts
isfree x (Φ ⇒ Ψ) = isfree x Φ or isfree x Ψ
isfree x (Φ ∧ Ψ) = isfree x Φ or isfree x Ψ
isfree x (Φ ∨ Ψ) = isfree x Φ or isfree x Ψ
isfree x (Λ y Φ) = not (x ≈ y) and isfree x Φ
isfree x (V y Φ) = not (x ≈ y) and isfree x Φ


_isNotFreeIn_ : (x : Variable) → (Φs : List Formula) → Set
x isNotFreeIn Φs = isTrue (not (any (isfree x) Φs))


{-# TERMINATING #-}
-- Todo: of course this terminates
sub_for_inside_ : Term → Term → Term → Term
suball : ∀{n} → Vec Term n → Term → Term → Vec Term n

sub (varterm x) for t inside r@(varterm y) with x ≈ y
...                                        | false = r
...                                        | true = t
sub (functerm _ _) for t inside r@(varterm x) = r
sub s@(varterm x) for t inside functerm f rs = functerm f (suball rs s t)
sub s@(functerm g qs) for t inside functerm f rs
                                       with (g ≈ f) and (qs vec≈ rs)
...                                    | false = functerm f (suball rs s t)
...                                    | true = t

suball xs s t = vecmap (sub_for_inside_ s t) xs

_[_/_] : Formula → Term → Term → Formula
atom r rs [ s / t ] = atom r (suball rs s t)
(α ⇒ β) [ s / t ] = (α [ s / t ]) ⇒ (β [ s / t ])
(α ∧ β) [ s / t ] = (α [ s / t ]) ∧ (β [ s / t ])
(α ∨ β) [ s / t ] = (α [ s / t ]) ∨ (β [ s / t ])
Λ x α [ s@(varterm y) / t ] with x ≈ y
...                         | false = Λ x (α [ s / t ])
...                         | true = Λ x α
Λ x α [ s@(functerm _ ss) / t ] = Λ x (α [ s / t ])
V x α [ s@(varterm y) / t ] with x ≈ y
...                         | false = V x (α [ s / t ])
...                         | true = V x α
V x α [ s@(functerm _ ss) / t ] = V x (α [ s / t ])


_∖_ : List Formula → Formula → List Formula
xs ∖ y = remove _≈_ y xs

infixl 6 _∖_


record Scheme : Set where
  constructor scheme
  field
    arity : ℕ
    name  : String
    func  : (Vec Formula arity) → Formula
