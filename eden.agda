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

infixr 10 _++_
infixr 20 _::_

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
  R   : Formula
  S   : Term → Formula
  _⇒_ : Formula → Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  Ε   : Formula

infixr 110 _∨_
infixr 120 _∧_
infixr 130 _⇒_


_≡_ : Formula → Formula → Bool
P ≡ P             = true
Q ≡ Q             = true
R ≡ R             = true
S t ≡ S s         = t == s
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
  Assume     :                  (f : Formula)                           → Deduction [ f ] f
  ArrowIntro : ∀{f afs}       → (Deduction afs f)     → (g : Formula)   → Deduction (afs discharging g) (g ⇒ f)
  ArrowElim  : ∀{f g ars ags} → Deduction ars (g ⇒ f) → Deduction ags g → Deduction (ars ++ ags) f
  ConjIntro  : ∀{f g afs ags} → Deduction afs f       → Deduction ags g → Deduction (afs ++ ags) (f ∧ g)
  ConjElim₁  : ∀{f g acs}     → Deduction acs (f ∧ g)                   → Deduction acs f
  ConjElim₂  : ∀{f g acs}     → Deduction acs (f ∧ g)                   → Deduction acs g
  DisjIntro₁ : ∀{f afs}       → Deduction afs f       → (g : Formula)   → Deduction afs (f ∨ g)
  DisjIntro₂ : ∀{f afs}       → Deduction afs f       → (g : Formula)   → Deduction afs (g ∨ f)
  DisjElim   : ∀{f g r ads als ars} → Deduction ads (f ∨ g) → Deduction als r → Deduction ars r → Deduction (ads ++ ((als discharging f) ++ (ars discharging g))) r



Conclusion : {f : Formula} → {afs : List Formula} → Deduction afs f → Formula
Conclusion {f} _ = f

-- Tests

test0 : Deduction [ P ] P
test0 = Assume P


test1 : Deduction (P ⇒ Q :: [ P ]) Q
test1 = ArrowElim (Assume (P ⇒ Q)) (Assume P)

test2 : Deduction [ Q ] (P ⇒ Q)
test2 = ArrowIntro (Assume Q) P

test3 : Deduction (P :: [ Q ]) (P ∧ Q)
test3 = ConjIntro (Assume P) (Assume Q)

test4 : Deduction [ P ∧ Q ] P
test4 = ConjElim₁ (Assume (P ∧ Q))

test5 : Deduction [ P ∧ Q ] Q
test5 = ConjElim₂ (Assume (P ∧ Q))

test6 : Deduction [ P ] (P ∨ Q)
test6 = DisjIntro₁ (Assume P) Q

test7 : Deduction [ P ] (Q ∨ P)
test7 = DisjIntro₂ (Assume P) Q

test8 : Deduction [] (P ⇒ (P ∨ Q))
test8 = ArrowIntro (DisjIntro₁ (Assume P) Q) P

test9 : Deduction (P ∨ Q :: P ⇒ R :: Q ⇒ R :: []) R
test9 = DisjElim (Assume (P ∨ Q)) (ArrowElim (Assume (P ⇒ R)) (Assume P)) (ArrowElim (Assume (Q ⇒ R)) (Assume Q))

