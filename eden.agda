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

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A


[_] : {A : Set} → A → List A
[ x ] = x :: []

_++_ : {A : Set} → List A → List A → List A
[] ++ ys        = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

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
(a ∧ b) ≡ (c ∧ d) = (a ≡ c) and (b ≡ d)
(a ∨ b) ≡ (c ∨ d) = (a ≡ c) and (b ≡ d)
_ ≡ _             = false


_discharging_ : List Formula → Formula → List Formula
[] discharging _        = []
(x :: xs) discharging y with (x ≡ y)
...                        | true  = (xs discharging y)
...                        | false = x :: (xs discharging y)


----------------------------------------

data Deduction : List Formula → Formula → Set where
  Assume     : (f : Formula) → Deduction [ f ] f
  ArrowIntro : {f : Formula} → {afs : List Formula} → (Deduction afs f) → (g : Formula) → Deduction (afs discharging g) (g ⇒ f)
  ArrowElim  : {f g : Formula} → {ars ags : List Formula} → Deduction ars (g ⇒ f) → Deduction ags g → Deduction (ars ++ ags) f
  ConjIntro  : {f g : Formula} → {afs ags : List Formula} → Deduction afs f → Deduction ags g → Deduction (afs ++ ags) (f ∧ g)
  ConjElim₁  : {f g : Formula} → {acs : List Formula} → Deduction acs (f ∧ g) → Deduction acs f
  ConjElim₂  : {f g : Formula} → {acs : List Formula} → Deduction acs (f ∧ g) → Deduction acs g
  DisjIntro₁ : {f : Formula} → {afs : List Formula} → Deduction afs f → (g : Formula) → Deduction afs (f ∨ g)
  DisjIntro₂ : {f : Formula} → {afs : List Formula} → Deduction afs f → (g : Formula) → Deduction afs (g ∨ f)


Conclusion : {f : Formula} → {afs : List Formula} → Deduction afs f → Formula
Conclusion {f} _ = f

-- Tests

test0 : Deduction [ P ] P
test0 = Assume P


test1 : Deduction (P :: [ P ⇒ Q ] ) Q
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
