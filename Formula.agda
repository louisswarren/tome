module Formula where

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



_-formula : ℕ → Set
(n)-formula = index height n


extract : ∀{n} → (n)-formula → Formula
extract (Φ , _) = Φ

open import Agda.Builtin.Equality


classify : Formula → Σ ℕ _-formula
classify Φ = height Φ , (Φ , refl)


undo : Formula → Formula
undo Φ with classify Φ
...    | n , nf = extract nf

undo' : ∀{n} → (n)-formula → (n)-formula
undo' nf with classify (extract nf)
undo' nf | fst , a = {!   !} , {!   !}
