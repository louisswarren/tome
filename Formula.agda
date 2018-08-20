module Formula where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma

open import Vec
open import Decidable
open import String

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

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

bottom = atom (mkprop "⊥") []

not notnot : Formula → Formula
not Φ = Φ ⇒ bottom
notnot Φ = not(not Φ)

--------------------------------------------------------------------------------
-- Surely there's something nicer than this?

private
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
  varEq (mkvar s) (mkvar t) with stringEq s t
  ...                       | yes refl = yes refl
  ...                       | no  neq  = no φ
                                        where φ : _
                                              φ refl = neq refl

  funcEq : Decidable≡ Function
  funcEq (mkfunc n s) (mkfunc m t) with stringEq s t
  ...                              | no  neq  = no φ
                                                where φ : _
                                                      φ refl = neq refl
  ...                              | yes refl with natEq n m
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
  ...                            | no  neq  = no φ where φ : _
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

  data _TermNotIn_ (t : Term) : ∀{n} → Vec Term n → Set where
    []   : t TermNotIn []
    var  : ∀{n} {xs : Vec Term n}
            → (x : Variable)
            → t ≢ (varterm x)
            → t TermNotIn xs
            → t TermNotIn (varterm x ∷ xs)
    func : ∀{n} {xs : Vec Term n}
            → (f : Function) → {ys : Vec Term (Function.arity f)} → t TermNotIn ys
            → t ≢ functerm f ys
            → t TermNotIn xs
            → t TermNotIn (functerm f ys ∷ xs)

  isTermNotIn : ∀{n} → (t : Term) → (ss : Vec Term n) → Dec (t TermNotIn ss)
  isTermNotIn t [] = yes []
  isTermNotIn t (s ∷ ss) with isTermNotIn t ss
  isTermNotIn t (s ∷ ss) | yes rst with termEq t s
  ...                              | yes x = no φ
                                            where φ : _
                                                  φ (var _ neq _)    = neq x
                                                  φ (func _ _ neq _) = neq x

  isTermNotIn t (varterm x₁ ∷ ss) | yes rst | no x = yes (var x₁ x rst)
  isTermNotIn t (functerm f x₁ ∷ ss) | yes rst | no x with isTermNotIn t x₁
  isTermNotIn t (functerm f x₁ ∷ ss) | yes rst | no x | yes x₂ = yes (func f x₂ x rst)
  isTermNotIn t (functerm f x₁ ∷ ss) | yes rst | no x | no x₂ = no φ
                                                                where φ : _
                                                                      φ (func f pf x₁ pf₁) = x₂ pf
  isTermNotIn t (s ∷ ss) | no isin = no φ
                                    where φ : _
                                          φ (var _ _ pf)    = isin pf
                                          φ (func _ _ _ pf) = isin pf

data _BoundIn_ : Term → Formula → Set where
  atom : ∀{t r} {xs : Vec Term (Relation.arity r)}
                  → t TermNotIn xs → t BoundIn (atom r xs)
  _⇒_  : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ⇒ β)
  _∧_  : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ∧ β)
  _∨_  : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ∨ β)
  Λ∣   : ∀ x α    → (varterm x) BoundIn Λ x α
  V∣   : ∀ x α    → (varterm x) BoundIn V x α
  Λ    : ∀{t α}   → ∀ x → t BoundIn α → t BoundIn Λ x α
  V    : ∀{t α}   → ∀ x → t BoundIn α → t BoundIn V x α

_isBoundIn_ : (t : Term) → (α : Formula) → Dec (t BoundIn α)
t isBoundIn atom r x = {!   !}
t isBoundIn (α ⇒ β) = {!   !}
t isBoundIn (α ∧ β) = {!   !}
t isBoundIn (α ∨ β) = {!   !}
t isBoundIn Λ x α = {!   !}
t isBoundIn V x α = {!   !}
t isBoundIn (α [ s / r ]) = {!   !}
