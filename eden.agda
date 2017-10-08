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
  Ε   : Formula


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

test0 : Deduction P
test0 = Assume P


test1 : Deduction Q
test1 = (ArrowElim (Assume (P ⇒ Q)) (Assume P))

test2 : Deduction (P ⇒ Q)
test2 = (ArrowIntro (Assume Q) P)
