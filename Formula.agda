module Formula where

open import Agda.Builtin.Bool
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

⊥ = propatom (mkprop "⊥")

¬ : Formula → Formula
¬ Φ = Φ ⇒ ⊥


height : Formula → ℕ
height (atom r ts) = zero
height (a ⇒ b)     = suc (maxℕ (height a) (height b))
height (a ∧ b)     = suc (maxℕ (height a) (height b))
height (a ∨ b)     = suc (maxℕ (height a) (height b))
height (Λ x a)     = suc (height a)
height (V x a)     = suc (height a)

relationcmp : ∀{n m} → (n)-aryRelationSymbol → (m)-aryRelationSymbol → Bool
relationcmp (mkrel n x) (mkrel m y) = n == m and primStringEquality x y

funccmp : ∀{n m} → (n)-aryFunctionSymbol → (m)-aryFunctionSymbol → Bool
funccmp (mkfunc n x) (mkfunc m y) = n == m and primStringEquality x y

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

