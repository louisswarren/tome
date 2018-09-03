module Formula where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Vec
open import Decidable


-- "Let a countably infinite set {vi | i ∈ N} of variables be given."
record Variable : Set where
  constructor mkvar
  field
    idx : ℕ


-- "For every natural number n ≥ 0 a ... set of n-ary relation symbols."
record Relation : Set where
  constructor mkrel
  field
    idx   : ℕ
    arity : ℕ

mkprop : ℕ → Relation
mkprop n = mkrel n zero


-- "For every natural number n ≥ 0 a ... set of n-ary function symbols."
record Function : Set where
  constructor mkfunc
  field
    idx   : ℕ
    arity : ℕ

mkconst : ℕ → Function
mkconst n = mkfunc n zero


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
--  from prime formulas."
data Formula : Set where
  atom   : (r : Relation) → Vec Term (Relation.arity r) → Formula
  _⇒_    : Formula  → Formula → Formula
  _∧_    : Formula  → Formula → Formula
  _∨_    : Formula  → Formula → Formula
  Λ      : Variable → Formula → Formula
  V      : Variable → Formula → Formula

infixr 105 _⇒_ _⇔_
infixr 106 _∨_
infixr 107 _∧_

_⇔_ : Formula → Formula → Formula
Φ ⇔ Ψ = (Φ ⇒ Ψ) ∧ (Ψ ⇒ Φ)


record Scheme : Set where
  constructor scheme
  field
    idx   : String
    arity : ℕ
    inst  : Vec Formula arity → Formula


-- Term freedom

data _TermNotIn_ (t : Term) : ∀{n} → Vec Term n → Set where
  []    : t TermNotIn []
  var∉  : ∀{n} {xs : Vec Term n}
            → (x : Variable)
            → t ≢ (varterm x)
            → t TermNotIn xs
            → t TermNotIn (varterm x ∷ xs)
  func∉ : ∀{n} {xs : Vec Term n}
            → (f : Function) → {ys : Vec Term (Function.arity f)} → t TermNotIn ys
            → t ≢ functerm f ys
            → t TermNotIn xs
            → t TermNotIn (functerm f ys ∷ xs)

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

----------------------------------------------------------------------------------
-- Computation requires decidable equality for the types above
-- Surely there's something nicer than this?

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

formulaEq : Decidable≡ Formula
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
formulaEq (atom r x) (β ⇒ β₁) = no (λ ())
formulaEq (atom r x) (β ∧ β₁) = no (λ ())
formulaEq (atom r x) (β ∨ β₁) = no (λ ())
formulaEq (atom r x) (Λ x₁ β) = no (λ ())
formulaEq (atom r x) (V x₁ β) = no (λ ())
formulaEq (α ⇒ α₁) (atom r x) = no (λ ())
formulaEq (α ⇒ α₁) (β ∧ β₁) = no (λ ())
formulaEq (α ⇒ α₁) (β ∨ β₁) = no (λ ())
formulaEq (α ⇒ α₁) (Λ x β) = no (λ ())
formulaEq (α ⇒ α₁) (V x β) = no (λ ())
formulaEq (α ∧ α₁) (atom r x) = no (λ ())
formulaEq (α ∧ α₁) (β ⇒ β₁) = no (λ ())
formulaEq (α ∧ α₁) (β ∨ β₁) = no (λ ())
formulaEq (α ∧ α₁) (Λ x β) = no (λ ())
formulaEq (α ∧ α₁) (V x β) = no (λ ())
formulaEq (α ∨ α₁) (atom r x) = no (λ ())
formulaEq (α ∨ α₁) (β ⇒ β₁) = no (λ ())
formulaEq (α ∨ α₁) (β ∧ β₁) = no (λ ())
formulaEq (α ∨ α₁) (Λ x β) = no (λ ())
formulaEq (α ∨ α₁) (V x β) = no (λ ())
formulaEq (Λ x α) (atom r x₁) = no (λ ())
formulaEq (Λ x α) (β ⇒ β₁) = no (λ ())
formulaEq (Λ x α) (β ∧ β₁) = no (λ ())
formulaEq (Λ x α) (β ∨ β₁) = no (λ ())
formulaEq (Λ x α) (V x₁ β) = no (λ ())
formulaEq (V x α) (atom r x₁) = no (λ ())
formulaEq (V x α) (β ⇒ β₁) = no (λ ())
formulaEq (V x α) (β ∧ β₁) = no (λ ())
formulaEq (V x α) (β ∨ β₁) = no (λ ())
formulaEq (V x α) (Λ x₁ β) = no (λ ())

--------------------------------------------------------------------------------

-- Term replacement

data [_][_/_]≡_ : ∀{n} → Vec Term n → Term → Term → Vec Term n → Set where
  []    : ∀{s t} → [ [] ][ s / t ]≡ []
  var≡  : ∀{n t} {xs ys : Vec Term n}
            → (x : Variable)
            → [ xs ][ varterm x / t ]≡ ys
            → [ varterm x ∷ xs ][ varterm x / t ]≡ (t ∷ ys)
  var≢  : ∀{n s t} {xs ys : Vec Term n}
            → (x : Variable)
            → s ≢ varterm x
            → [ xs ][ s / t ]≡ ys
            → [ varterm x ∷ xs ][ s / t ]≡ (varterm x ∷ ys)
  func≡ : ∀{n t} {xs ys : Vec Term n}
            → (f : Function) → ∀{us}
            → [ xs ][ functerm f us / t ]≡ ys
            → [ functerm f us ∷ xs ][ functerm f us / t ]≡ (t ∷ ys)
  func≢ : ∀{n s t} {xs ys : Vec Term n}
            → (f : Function) → ∀{us vs}
            → s ≢ functerm f us
            → [ us ][ s / t ]≡ vs
            → [ xs ][ s / t ]≡ ys
            → [ functerm f us ∷ xs ][ s / t ]≡ (functerm f vs ∷ ys)

data _[_/_]≡_ : Formula → Term → Term → Formula → Set where
  ident : ∀ α t → α [ t / t ]≡ α
  atom  : ∀{s t} → (r : Relation) → ∀{xs ys} → [ xs ][ s / t ]≡ ys → (atom r xs) [ s / t ]≡ (atom r ys)
  _⇒_   : ∀{α α′ β β′ s t} → α [ s / t ]≡ α′ → β [ s / t ]≡ β′ → (α ⇒ β) [ s / t ]≡ (α′ ⇒ β′)
  _∧_   : ∀{α α′ β β′ s t} → α [ s / t ]≡ α′ → β [ s / t ]≡ β′ → (α ∧ β) [ s / t ]≡ (α′ ∧ β′)
  _∨_   : ∀{α α′ β β′ s t} → α [ s / t ]≡ α′ → β [ s / t ]≡ β′ → (α ∨ β) [ s / t ]≡ (α′ ∨ β′)
  Λ∣    : ∀{α x t} → (Λ x α) [ varterm x / t ]≡ (Λ x α)
  V∣    : ∀{α x t} → (V x α) [ varterm x / t ]≡ (V x α)
  Λ     : ∀{α β x s t} → s ≢ (varterm x) → α [ s / t ]≡ β → (Λ x α) [ s / t ]≡ (Λ x β)
  V     : ∀{α β x s t} → s ≢ (varterm x) → α [ s / t ]≡ β → (V x α) [ s / t ]≡ (V x β)
