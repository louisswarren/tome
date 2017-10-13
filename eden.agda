open import common

module eden where

----------------------------------------

data False  : Set where
record True : Set where

isTrue : Bool → Set
isTrue true  = True
isTrue false = False

----------------------------------------

data Term : Set where
  NamedTerm : ℕ → Term
  X : Term
  Y : Term

TermEq : Term → Term → Bool
TermEq (NamedTerm n) (NamedTerm m) = n == m
TermEq X X                         = true
TermEq Y Y                         = true
TermEq _ _                         = false


----------------------------------------

data Formula : Set where
  P   : Formula
  Q   : Formula
  R   : Formula
  S   : Term → Formula
  _⇒_ : Formula → Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  Α   : Term → Formula → Formula
  Ε   : Term → Formula → Formula

infixr 110 _∨_
infixr 120 _∧_
infixr 130 _⇒_


_≡_ : Formula → Formula → Bool
P ≡ P             = true
Q ≡ Q             = true
R ≡ R             = true
S t ≡ S s         = TermEq t s
(a ⇒ b) ≡ (c ⇒ d) = (a ≡ c) and (b ≡ d)
(a ∧ b) ≡ (c ∧ d) = (a ≡ c) and (b ≡ d)
(a ∨ b) ≡ (c ∨ d) = (a ≡ c) and (b ≡ d)
_ ≡ _             = false

_discharging_ : List Formula → Formula → List Formula
[] discharging _        = []
(x :: xs) discharging y with (x ≡ y)
...                        | true  = (xs discharging y)
...                        | false = x :: (xs discharging y)


_freein_ : Term → Formula → Bool
t freein P       = false
t freein Q       = false
t freein R       = false
t freein (S n)   = not (TermEq t n)
t freein (a ⇒ b) = (t freein a) or (t freein b)
t freein (a ∧ b) = (t freein a) or (t freein b)
t freein (a ∨ b) = (t freein a) or (t freein b)
t freein (Ε n a) = (not (TermEq t n)) and (t freein a)
t freein (Α n a) = (not (TermEq t n)) and (t freein a)


data _NotFreeIn_ (t : Term) : List Formula → Set where
  AllClosed : t NotFreeIn []
  Recur     : ∀{f fs} → {p : isTrue (not (t freein f))} → t NotFreeIn fs → t NotFreeIn (f :: fs)


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
  UniGIntro  : ∀{f afs t} → (t NotFreeIn afs) → Deduction afs f → (t : Term) → Deduction afs (Α t f)
  UniGElim   : ∀{f afs t} → Deduction afs (Α t f) → Deduction afs f
  ExiGIntro  : ∀{f afs} → Deduction afs f → (t : Term) → Deduction afs (Ε t f)
  --- Not necessarily valid - cannot use an already existing term
  ExiGElim   : ∀{f g afs gfs t} → t NotFreeIn [ g ] → Deduction afs (Ε t f) → Deduction gfs g → Deduction (afs ++ (gfs discharging f)) g



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

test10terms : X NotFreeIn [ (Α X (S X ∧ P)) ]
test10terms = Recur AllClosed

test10 : Deduction [ (Α X (S X ∧ P)) ] (Α X (S X))
test10 = UniGIntro test10terms (ConjElim₁ (UniGElim (Assume (Α X (S X ∧ P))))) X

test11 : Deduction [ (Α X (S X)) ] (S X)
test11 = UniGElim (Assume (Α X (S X)))

test12 : Deduction [ S X ] (Ε X (S X))
test12 = ExiGIntro (Assume (S X)) X

test13 : Deduction ((Ε X (S X)) :: [ Α X ((S X) ⇒ P) ]) P
test13 = ExiGElim (Recur AllClosed) (Assume (Ε X (S X))) (ArrowElim (UniGElim (Assume (Α X ((S X) ⇒ P)))) (Assume (S X)))

