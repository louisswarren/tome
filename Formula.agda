module Formula where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String
open import common



-- "Let a countably infinite set {vi | i ∈ N} of variables be given."
data Variable : Set where
  var : String → Variable



-- "For every natural number n ≥ 0 a ... set of n-ary relation symbols."
data _-aryRelationSymbol : ℕ → Set where
  mkrel : (n : ℕ) → String → (n)-aryRelationSymbol

PropositionalSymbol = (zero)-aryRelationSymbol
mkprop : String → PropositionalSymbol
mkprop s = mkrel zero s

-- "For every natural number n ≥ 0 a ... set of n-ary function symbols."
data _-aryFunctionSymbol : ℕ → Set where
  mkfunc : (n : ℕ) → String → (n)-aryFunctionSymbol

Constant = (zero)-aryFunctionSymbol
mkconst : String → Constant
mkconst s = mkfunc zero s



-- "Terms are inductively defined as follows.
--  (i)   Every variable is a term.
--  (ii)  Every constant is a term.
--  (iii) If t1, . . . , tn are terms and f is an n-ary function symbol with
--        n ≥ 1, then f(t1 , . . . , tn ) is a term."

data Term : Set where
  varterm  : Variable → Term
  functerm : ∀{n} → (n)-aryFunctionSymbol → Vec Term n → Term

constterm : Constant → Term
constterm c = functerm c []


-- "If t1, . . . , tn are terms and R is an n-ary relation symbol, then
--  R(t1, . . . , tn ) is a prime formula ... Formulas are inductively defined
--- from prime formulas.
data Formula : Set where
  atom : ∀{n} → (n)-aryRelationSymbol → Vec Term n → Formula
  _⇒_ : Formula → Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  Λ   : Variable → Formula → Formula
  V   : Variable → Formula → Formula

propatom : PropositionalSymbol → Formula
propatom p = atom p []

infixr 105 _⇒_
infixr 106 _∨_
infixr 107 _∧_

⊥ = propatom (mkprop "⊥")

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
-- Clumsy way of defining extensional equality of formulae as just being as
-- intensional equality

relationcmp : ∀{n m} → (n)-aryRelationSymbol → (m)-aryRelationSymbol → Bool
relationcmp (mkrel n x) (mkrel m y) = n == m and primStringEquality x y

funccmp : ∀{n m} → (n)-aryFunctionSymbol → (m)-aryFunctionSymbol → Bool
funccmp (mkfunc n x) (mkfunc m y) = n == m and primStringEquality x y

varcmp : Variable → Variable → Bool
varcmp (var x) (var y) = primStringEquality x y

termveccmp : ∀{n m} → Vec Term n → Vec Term m → Bool

termcmp : Term → Term → Bool
termcmp (varterm (var x)) (varterm (var y)) = primStringEquality x y
termcmp (functerm x xs) (functerm y ys)     = (funccmp x y) and termveccmp xs ys
termcmp _                 _                 = false

termveccmp []       []       = true
termveccmp (x ∷ xs) (y ∷ ys) = termcmp x y and termveccmp xs ys
termveccmp _        _        = false

formulacmp : Formula → Formula → Bool
formulacmp (atom r xs) (atom s ys) = (relationcmp r s) and (termveccmp xs ys)
formulacmp (a ⇒ b) (c ⇒ d) = (formulacmp a c) and (formulacmp b d)
formulacmp (a ∧ b) (c ∧ d) = (formulacmp a c) and (formulacmp b d)
formulacmp (a ∨ b) (c ∨ d) = (formulacmp a c) and (formulacmp b d)
formulacmp _       _       = false


--------------------------------------------------------------------------------

{-# NON_TERMINATING #-}
-- Todo: of course this terminates
appearsin : Variable → Term → Bool
appearsin x (varterm y) = varcmp x y
appearsin x (functerm _ ys) = vecany (appearsin x) ys



isfree : Variable → Formula → Bool
isfree x (atom _ ts) = vecany (appearsin x) ts
isfree x (Φ ⇒ Ψ) = isfree x Φ or isfree x Ψ
isfree x (Φ ∧ Ψ) = isfree x Φ or isfree x Ψ
isfree x (Φ ∨ Ψ) = isfree x Φ or isfree x Ψ
isfree x (Λ y Φ) = not (varcmp x y) and isfree x Φ
isfree x (V y Φ) = not (varcmp x y) and isfree x Φ


_isNotFreeIn_ : (x : Variable) → (Φs : List Formula) → Set
x isNotFreeIn Φs = all (isfree x) Φs ≡ true


{-# NON_TERMINATING #-}
-- Todo: of course this terminates
sub_for_inside_ : Term → Term → Term → Term
suball : ∀{n} → Vec Term n → Term → Term → Vec Term n

sub (varterm x) for t inside r@(varterm y) with varcmp x y
...                                        | false = r
...                                        | true = t
sub (functerm _ _) for t inside r@(varterm x) = r
sub s@(varterm x) for t inside functerm f rs = functerm f (suball rs s t)
sub s@(functerm g qs) for t inside functerm f rs
                                       with (funccmp g f) and (termveccmp qs rs)
...                                    | false = functerm f (suball rs s t)
...                                    | true = t

suball xs s t = vecmap (sub_for_inside_ s t) xs

_[_/_] : Formula → Term → Term → Formula
atom r rs [ s / t ] = atom r (suball rs s t)
(α ⇒ β) [ s / t ] = (α [ s / t ]) ⇒ (β [ s / t ])
(α ∧ β) [ s / t ] = (α [ s / t ]) ∧ (β [ s / t ])
(α ∨ β) [ s / t ] = (α [ s / t ]) ∨ (β [ s / t ])
Λ x α [ s@(varterm y) / t ] with varcmp x y
...                         | false = Λ x (α [ s / t ])
...                         | true = Λ x α
Λ x α [ s@(functerm _ ss) / t ] = Λ x (α [ s / t ])
V x α [ s@(varterm y) / t ] with varcmp x y
...                         | false = V x (α [ s / t ])
...                         | true = V x α
V x α [ s@(functerm _ ss) / t ] = V x (α [ s / t ])
