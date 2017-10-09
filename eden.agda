module eden where

----------------------------------------

data Bool : Set where
  true  : Bool
  false : Bool

_or_ : Bool → Bool → Bool
true or _  = true
false or b = b

_and_ : Bool → Bool → Bool
false and _ = false
true and b  = b


----------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

NatEq : ℕ → ℕ → Bool
NatEq zero zero       = true
NatEq (suc n) (suc m) = NatEq n m
NatEq _ _             = false

----------------------------------------
data Term : Set where
  NamedTerm : ℕ → Term
  X : Term
  Y : Term

_==_ : Term → Term → Bool
NamedTerm n == NamedTerm m = NatEq n m
X == X                     = true
Y == Y                     = true
_ == _                     = false

----------------------------------------

data Formula : Set where
  P   : Formula
  Q   : Formula
  R   : Term → Formula
  _⇒_ : Formula → Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  Ε   : Formula

infixr 10 _∨_
infixr 20 _∧_
infixr 30 _⇒_


_≡_ : Formula → Formula → Bool
P ≡ P             = true
Q ≡ Q             = true
R t ≡ R s         = t == s
(a ⇒ b) ≡ (c ⇒ d) = (a ≡ c) and (b ≡ d)
_ ≡ _             = false

lhs : Formula → Formula
lhs (a ⇒ _) = a
lhs _ = Ε

rhs : Formula → Formula
rhs (_ ⇒ b) = b
rhs _ = Ε


----------------------------------------

data Deduction : Formula → Set where
  Assume     : (f : Formula) → Deduction f
  ArrowIntro : {f : Formula} → (Deduction f) → (g : Formula) → Deduction (g ⇒ f)
  ArrowElim  : {f g : Formula} → Deduction (g ⇒ f) → Deduction g → Deduction f
  ConjIntro  : {f g : Formula} → Deduction f → Deduction g → Deduction (f ∧ g)
  ConjElim₁  : {f g : Formula} → Deduction (f ∧ g) → Deduction f
  ConjElim₂  : {f g : Formula} → Deduction (f ∧ g) → Deduction g
  DisjIntro₁ : {f : Formula} → Deduction f → (g : Formula) → Deduction (f ∨ g)
  DisjIntro₂ : {f : Formula} → Deduction f → (g : Formula) → Deduction (g ∨ f)


-- Shorthands
ConjElim : {f g : Formula} → Deduction (f ∧ g) → Deduction f
ConjElim = ConjElim₁

DisjIntro : {f : Formula} → Deduction f → (g : Formula) → Deduction (f ∨ g)
DisjIntro = DisjIntro₁


Conclusion : {f : Formula} → Deduction f → Formula
Conclusion {f} _ = f

-- Tests

test0 : Deduction P
test0 = Assume P


test1 : Deduction Q
test1 = ArrowElim (Assume (P ⇒ Q)) (Assume P)

test2 : Deduction (P ⇒ Q)
test2 = ArrowIntro (Assume Q) P

test3 : Deduction (P ∧ Q)
test3 = ConjIntro (Assume P) (Assume Q)

test4 : Deduction P
test4 = ConjElim₁ (Assume (P ∧ Q))

test5 : Deduction Q
test5 = ConjElim₂ (Assume (P ∧ Q))

test6 : Deduction (P ∨ Q)
test6 = DisjIntro₁ (Assume P) Q

test7 : Deduction (Q ∨ P)
test7 = DisjIntro₂ (Assume P) Q
