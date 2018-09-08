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


-- "For every natural number n ≥ 0 a ... set of n-ary function symbols."
record Function : Set where
  constructor mkfunc
  field
    idx   : ℕ
    arity : ℕ


-- "Terms are inductively defined as follows.
--  (i)   Every variable is a term.
--  (ii)  Every constant is a term.
--  (iii) If t1, . . . , tn are terms and f is an n-ary function symbol with
--        n ≥ 1, then f(t1 , . . . , tn ) is a term."
data Term : Set where
  varterm  : Variable → Term
  functerm : (f : Function) → Vec Term (Function.arity f) → Term


-- "For every natural number n ≥ 0 a ... set of n-ary relation symbols."
record Relation : Set where
  constructor mkrel
  field
    idx   : ℕ
    arity : ℕ


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

_⇔_ : Formula → Formula → Formula
Φ ⇔ Ψ = (Φ ⇒ Ψ) ∧ (Ψ ⇒ Φ)

infixr 105 _⇒_ _⇔_
infixr 106 _∨_
infixr 107 _∧_


record Scheme : Set where
  constructor scheme
  field
    idx   : String
    arity : ℕ
    inst  : Vec Formula arity → Formula


-- Variable freedom

data _BoundInTerms_ (x : Variable) : ∀{n} → Vec Term n → Set where
  []    : x BoundInTerms []
  var∉  : ∀{n} {xs : Vec Term n}
            → (y : Variable)
            → x ≢ y
            → x BoundInTerms xs
            → x BoundInTerms (varterm y ∷ xs)
  func∉ : ∀{n} {xs : Vec Term n}
            → (f : Function) → {us : Vec Term (Function.arity f)}
            → x BoundInTerms us
            → x BoundInTerms xs
            → x BoundInTerms (functerm f us ∷ xs)

data _BoundIn_ : Variable → Formula → Set where
  atom : ∀{t r} {xs : Vec Term (Relation.arity r)}
                  → t BoundInTerms xs → t BoundIn (atom r xs)
  _⇒_  : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ⇒ β)
  _∧_  : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ∧ β)
  _∨_  : ∀{t α β} → t BoundIn α → t BoundIn β → t BoundIn (α ∨ β)
  Λ∣   : ∀ x α    → x BoundIn Λ x α
  V∣   : ∀ x α    → x BoundIn V x α
  Λ    : ∀{t α}   → ∀ x → t BoundIn α → t BoundIn Λ x α
  V    : ∀{t α}   → ∀ x → t BoundIn α → t BoundIn V x α


-- Variable replacement

data [_][_/_]≡_ : ∀{n} → Vec Term n → Variable → Term → Vec Term n → Set where
  []   : ∀{x t} → [ [] ][ x / t ]≡ []
  var≡ : ∀{n t} {xs ys : Vec Term n}
           → (x : Variable)
           → [ xs ][ x / t ]≡ ys
           → [ varterm x ∷ xs ][ x / t ]≡ (t ∷ ys)
  var≢ : ∀{n x t} {xs ys : Vec Term n}
           → (v : Variable)
           → x ≢ v
           → [ xs ][ x / t ]≡ ys
           → [ varterm v ∷ xs ][ x / t ]≡ (varterm v ∷ ys)
  func : ∀{n x t} {xs ys : Vec Term n}
           → (f : Function) → ∀{us vs}
           → [ us ][ x / t ]≡ vs
           → [ xs ][ x / t ]≡ ys
           → [ functerm f us ∷ xs ][ x / t ]≡ (functerm f vs ∷ ys)

data _[_/_]≡_ : Formula → Variable → Term → Formula → Set where
  ident : ∀ α x → α [ x / varterm x ]≡ α
  atom  : ∀{x t}
            → (r : Relation) → {xs ys : Vec Term (Relation.arity r)}
            → [ xs ][ x / t ]≡ ys → (atom r xs) [ x / t ]≡ (atom r ys)
  _⇒_   : ∀{α α′ β β′ x t}
            → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ⇒ β) [ x / t ]≡ (α′ ⇒ β′)
  _∧_   : ∀{α α′ β β′ x t}
            → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∧ β) [ x / t ]≡ (α′ ∧ β′)
  _∨_   : ∀{α α′ β β′ x t}
            → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∨ β) [ x / t ]≡ (α′ ∨ β′)
  Λ∣    : ∀{t} → (x : Variable) → (α : Formula) → (Λ x α) [ x / t ]≡ (Λ x α)
  V∣    : ∀{t} → (x : Variable) → (α : Formula) → (V x α) [ x / t ]≡ (V x α)
  Λ     : ∀{α β x v t} → v ≢ x → α [ v / t ]≡ β → (Λ x α) [ v / t ]≡ (Λ x β)
  V     : ∀{α β x v t} → v ≢ x → α [ v / t ]≡ β → (V x α) [ v / t ]≡ (V x β)


--------------------------------------------------------------------------------
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
...                            | no  neq  = no φ
                                            where φ : _
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
formulaEq (atom r x) (β ⇒ β₁)   = no (λ ())
formulaEq (atom r x) (β ∧ β₁)   = no (λ ())
formulaEq (atom r x) (β ∨ β₁)   = no (λ ())
formulaEq (atom r x) (Λ x₁ β)   = no (λ ())
formulaEq (atom r x) (V x₁ β)   = no (λ ())
formulaEq (α ⇒ α₁)   (atom r x) = no (λ ())
formulaEq (α ⇒ α₁)   (β ∧ β₁)   = no (λ ())
formulaEq (α ⇒ α₁)   (β ∨ β₁)   = no (λ ())
formulaEq (α ⇒ α₁)   (Λ x β)    = no (λ ())
formulaEq (α ⇒ α₁)   (V x β)    = no (λ ())
formulaEq (α ∧ α₁)   (atom r x) = no (λ ())
formulaEq (α ∧ α₁)   (β ⇒ β₁)   = no (λ ())
formulaEq (α ∧ α₁)   (β ∨ β₁)   = no (λ ())
formulaEq (α ∧ α₁)   (Λ x β)    = no (λ ())
formulaEq (α ∧ α₁)   (V x β)    = no (λ ())
formulaEq (α ∨ α₁)   (atom r x) = no (λ ())
formulaEq (α ∨ α₁)   (β ⇒ β₁)   = no (λ ())
formulaEq (α ∨ α₁)   (β ∧ β₁)   = no (λ ())
formulaEq (α ∨ α₁)   (Λ x β)    = no (λ ())
formulaEq (α ∨ α₁)   (V x β)    = no (λ ())
formulaEq (Λ x α)   (atom r x₁) = no (λ ())
formulaEq (Λ x α)   (β ⇒ β₁)    = no (λ ())
formulaEq (Λ x α)   (β ∧ β₁)    = no (λ ())
formulaEq (Λ x α)   (β ∨ β₁)    = no (λ ())
formulaEq (Λ x α)   (V x₁ β)    = no (λ ())
formulaEq (V x α)   (atom r x₁) = no (λ ())
formulaEq (V x α)   (β ⇒ β₁)    = no (λ ())
formulaEq (V x α)   (β ∧ β₁)    = no (λ ())
formulaEq (V x α)   (β ∨ β₁)    = no (λ ())
formulaEq (V x α)   (Λ x₁ β)    = no (λ ())
