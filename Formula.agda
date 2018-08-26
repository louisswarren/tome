module Formula where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma


open import Vec
open import Decidable
open import String


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


-- An n-ary scheme is a named n-ary function on formulae
record Scheme : Set where
  constructor scheme
  field
    name  : String
    arity : ℕ
    inst  : Vec Formula arity → Formula


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

  relEq : Decidable≡ Relation
  relEq (mkrel n s) (mkrel m t) with stringEq s t
  ...                           | no  neq  = no φ
                                             where φ : _
                                                   φ refl = neq refl
  ...                           | yes refl with natEq n m
  ...                                      | yes refl = yes refl
  ...                                      | no  neq  = no φ
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

postulate formulaEq : Decidable≡ Formula

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

-- Vim macros generated this
_isBoundIn_ : (t : Term) → (α : Formula) → Dec (t BoundIn α)
t isBoundIn atom r xs with isTermNotIn t xs
(t isBoundIn atom r xs) | yes x = yes (atom x)
(t isBoundIn atom r xs) | no x = no φ
  where φ : _
        φ (atom x₁) = x x₁
t isBoundIn (α ⇒ β) with t isBoundIn α
(t isBoundIn (α ⇒ β)) | yes x with t isBoundIn β
(t isBoundIn (α ⇒ β)) | yes x | yes x₁ = yes (x ⇒ x₁)
(t isBoundIn (α ⇒ β)) | yes x | no x₁ = no φ
  where φ : _
        φ (pf ⇒ pf₁) = x₁ pf₁
(t isBoundIn (α ⇒ β)) | no x = no φ
  where φ : _
        φ (pf ⇒ pf₁) = x pf
t isBoundIn (α ∧ β) with t isBoundIn α
(t isBoundIn (α ∧ β)) | yes x with t isBoundIn β
(t isBoundIn (α ∧ β)) | yes x | yes x₁ = yes (x ∧ x₁)
(t isBoundIn (α ∧ β)) | yes x | no x₁ = no φ
  where φ : _
        φ (pf ∧ pf₁) = x₁ pf₁
(t isBoundIn (α ∧ β)) | no x = no φ
  where φ : _
        φ (pf ∧ pf₁) = x pf
t isBoundIn (α ∨ β) with t isBoundIn α
(t isBoundIn (α ∨ β)) | yes x with t isBoundIn β
(t isBoundIn (α ∨ β)) | yes x | yes x₁ = yes (x ∨ x₁)
(t isBoundIn (α ∨ β)) | yes x | no x₁ = no φ
  where φ : _
        φ (pf ∨ pf₁) = x₁ pf₁
(t isBoundIn (α ∨ β)) | no x = no φ
  where φ : _
        φ (pf ∨ pf₁) = x pf
t isBoundIn Λ x α with termEq t (varterm x)
(.(varterm x) isBoundIn Λ x α) | yes refl = yes (Λ∣ x α)
(t isBoundIn Λ x α) | no x₁ with t isBoundIn α
(t isBoundIn Λ x α) | no x₁ | yes x₂ = yes (Λ x x₂)
(t isBoundIn Λ x α) | no x₁ | no x₂ = no φ
  where φ : _
        φ (Λ∣ x α) = x₁ refl
        φ (Λ x pf) = x₂ pf
t isBoundIn V x α with termEq t (varterm x)
(.(varterm x) isBoundIn V x α) | yes refl = yes (V∣ x α)
(t isBoundIn V x α) | no x₁ with t isBoundIn α
(t isBoundIn V x α) | no x₁ | yes x₂ = yes (V x x₂)
(t isBoundIn V x α) | no x₁ | no x₂ = no φ
  where φ : _
        φ (V∣ x α) = x₁ refl
        φ (V x pf) = x₂ pf


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

[_][_/_]′ : ∀{n} → (xs : Vec Term n) → (s t : Term) → Σ (Vec Term n) [ xs ][ s / t ]≡_
[ [] ][ s / t ]′ = [] , []
[ x ∷ xs ][ s / t ]′ with termEq s x
[ varterm x ∷ xs ][ .(varterm x) / t ]′ | yes refl with [ xs ][ varterm x / t ]′
[ varterm x ∷ xs ][ .(varterm x) / t ]′ | yes refl | ys , pf = (t ∷ ys) , var≡ x pf
[ functerm f us ∷ xs ][ .(functerm f us) / t ]′ | yes refl with [ xs ][ functerm f us / t ]′
[ functerm f us ∷ xs ][ .(functerm f us) / t ]′ | yes refl | ys , pf = (t ∷ ys) , func≡ f pf
[ x ∷ xs ][ s / t ]′ | no neq with [ xs ][ s / t ]′
[ varterm x ∷ xs ][ s / t ]′ | no neq | ys , pf = (varterm x ∷ ys) , var≢ x neq pf
[ functerm f us ∷ xs ][ s / t ]′ | no neq | ys , pf with [ us ][ s / t ]′
[ functerm f us ∷ xs ][ s / t ]′ | no neq | ys , pf | vs , pf′ = (functerm f vs ∷ ys) , func≢ f neq pf′ pf

[_][_/_] : ∀{n} → (xs : Vec Term n) → (s t : Term) → Vec Term n
[ xs ][ s / t ] = fst [ xs ][ s / t ]′

data _[_/_]≡_ : Formula → Term → Term → Formula → Set where
  atom : ∀{s t} → (r : Relation) → ∀{xs ys} → [ xs ][ s / t ]≡ ys → (atom r xs) [ s / t ]≡ (atom r ys)
  _⇒_  : ∀{α α′ β β′ s t} → α [ s / t ]≡ α′ → β [ s / t ]≡ β′ → (α ⇒ β) [ s / t ]≡ (α′ ⇒ β′)
  _∧_  : ∀{α α′ β β′ s t} → α [ s / t ]≡ α′ → β [ s / t ]≡ β′ → (α ∧ β) [ s / t ]≡ (α′ ∧ β′)
  _∨_  : ∀{α α′ β β′ s t} → α [ s / t ]≡ α′ → β [ s / t ]≡ β′ → (α ∨ β) [ s / t ]≡ (α′ ∨ β′)
  Λ∣   : ∀{α x t} → (Λ x α) [ varterm x / t ]≡ (Λ x α)
  V∣   : ∀{α x t} → (V x α) [ varterm x / t ]≡ (V x α)
  Λ    : ∀{α β x s t} → s ≢ (varterm x) → α [ s / t ]≡ β → (Λ x α) [ s / t ]≡ β
  V    : ∀{α β x s t} → s ≢ (varterm x) → α [ s / t ]≡ β → (V x α) [ s / t ]≡ β

_[_/_]′ : (α : Formula) → (s t : Term) → Σ Formula (α [ s / t ]≡_)
atom r xs [ s / t ]′ with [ xs ][ s / t ]′
...                  | ys , pf = atom r ys , atom r pf
(α ⇒ β)   [ s / t ]′ with (α [ s / t ]′) , (β [ s / t ]′)
...                  | (α′ , αpf) , (β' , βpf) = α′ ⇒ β' , αpf ⇒ βpf
(α ∧ β)   [ s / t ]′ with (α [ s / t ]′) , (β [ s / t ]′)
...                  | (α′ , αpf) , (β' , βpf) = α′ ∧ β' , αpf ∧ βpf
(α ∨ β)   [ s / t ]′ with (α [ s / t ]′) , (β [ s / t ]′)
...                  | (α′ , αpf) , (β' , βpf) = α′ ∨ β' , αpf ∨ βpf
Λ x α     [ s / t ]′ with termEq s (varterm x)
...                  | yes refl = Λ x α , Λ∣
...                  | no neq with α [ s / t ]′
...                           | α′ , pf = α′ , Λ neq pf
V x α     [ s / t ]′ with termEq s (varterm x)
...                  | yes refl = V x α , V∣
...                  | no neq with α [ s / t ]′
...                           | α′ , pf = α′ , V neq pf

_[_/_] : (α : Formula) → (s t : Term) → Formula
α [ s / t ] = fst (α [ s / t ]′)

postulate uniqueSub : ∀ α β γ s t → α [ s / t ]≡ β → α [ s / t ]≡ γ → β ≡ γ

repWitness : ∀{α β s t} → α [ s / t ]≡ β → α [ s / t ] ≡ β
repWitness {α} {β} {s} {t} rep with α [ s / t ]′
repWitness {α} {β} {s} {t} rep | a′ , pf = uniqueSub α a′ β s t pf rep
