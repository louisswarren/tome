module eden where

----------------------------------------

data Bool : Set where
  true  : Bool
  false : Bool

_∨_ : Bool → Bool → Bool
true ∨ _  = true
false ∨ b = b

_∧_ : Bool → Bool → Bool
false ∧ _ = false
true ∧ b  = b


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
  Ε   : Formula

_≡_ : Formula → Formula → Bool
P ≡ P             = true
Q ≡ Q             = true
R t ≡ R s         = t == s
(a ⇒ b) ≡ (c ⇒ d) = (a ≡ c) ∧ (b ≡ d)
_ ≡ _             = false

lhs : Formula → Formula
lhs (a ⇒ _) = a
lhs _ = Ε

rhs : Formula → Formula
rhs (_ ⇒ b) = b
rhs _ = Ε


----------------------------------------

data Deduction : Set where
  Assumption : Formula → Deduction
  ArrowIntro : Deduction → Formula → Deduction
  ArrowElim  : Deduction → Deduction → Deduction


resolve : Deduction → Formula
resolve (Assumption f)   = f
resolve (ArrowIntro Φ f) = f ⇒ (resolve Φ)
resolve (ArrowElim Φ Ψ)  with (lhs (resolve Φ)) ≡ (resolve Ψ)
...                         | true  = rhs (resolve Φ)
...                         | false = Ε



test1 : Formula
test1 = resolve (ArrowElim (Assumption (P ⇒ Q)) (Assumption P))

test2 : Formula
test2 = resolve (ArrowIntro (Assumption Q) P)
