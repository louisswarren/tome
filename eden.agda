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
  ⊥   : Formula
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


¬ : Formula → Formula
¬ a = a ⇒ ⊥


rename : Formula → Term → Term → Formula
rename ⊥ _ _       = ⊥
rename P _ _       = P
rename Q _ _       = Q
rename R _ _       = R
rename (S t) x y   with (TermEq t x)
...                   | true  = S y
...                   | false = S t
rename (a ⇒ b) x y = (rename a x y) ⇒ (rename b x y)
rename (a ∧ b) x y = (rename a x y) ∧ (rename b x y)
rename (a ∨ b) x y = (rename a x y) ∨ (rename b x y)
rename (Α t f) x y with (TermEq t x)
...                   | true  = Α t f
...                   | false = Α t (rename f x y)
rename (Ε t f) x y with (TermEq t x)
...                   | true  = Ε t f
...                   | false = Ε t (rename f x y)


_≡_ : Formula → Formula → Bool
⊥ ≡ ⊥             = true
P ≡ P             = true
Q ≡ Q             = true
R ≡ R             = true
S t ≡ S s         = TermEq t s
(a ⇒ b) ≡ (c ⇒ d) = (a ≡ c) and (b ≡ d)
(a ∧ b) ≡ (c ∧ d) = (a ≡ c) and (b ≡ d)
(a ∨ b) ≡ (c ∨ d) = (a ≡ c) and (b ≡ d)
(Α t f) ≡ (Α s g) = (rename f t s) ≡ g
(Ε t f) ≡ (Ε s g) = (rename f t s) ≡ g
_ ≡ _             = false


_∖_ : List Formula → Formula → List Formula
[] ∖ _        = []
(x :: xs) ∖ y with (x ≡ y)
...              | true  = (xs ∖ y)
...              | false = x :: (xs ∖ y)

infixl 200 _∖_


_freein_ : Term → Formula → Bool
t freein ⊥       = false
t freein P       = false
t freein Q       = false
t freein R       = false
t freein (S n)   = (TermEq t n)
t freein (a ⇒ b) = (t freein a) or (t freein b)
t freein (a ∧ b) = (t freein a) or (t freein b)
t freein (a ∨ b) = (t freein a) or (t freein b)
t freein (Ε n a) = (not (TermEq t n)) and (t freein a)
t freein (Α n a) = (not (TermEq t n)) and (t freein a)


data _NotFreeIn_ (t : Term) : List Formula → Set where
  AllClosed : t NotFreeIn []
  Recur     : ∀{Γ p}
              → {_ : isTrue (not (t freein p))}
              → t NotFreeIn Γ
              → t NotFreeIn (p :: Γ)


----------------------------------------

data Deduction : List Formula → Formula → Set where
  Assume     : (p : Formula)
               → Deduction [ p ] p

  ArrowIntro : ∀{Γ q}
               → (Deduction Γ q)
               → (p : Formula)
               → Deduction (Γ ∖ p) (p ⇒ q)

  ArrowElim  : ∀{Γ₁ Γ₂ p q}
               → Deduction Γ₁ (p ⇒ q)
               → Deduction Γ₂ p
               → Deduction (Γ₁ ++ Γ₂) q

  ConjIntro  : ∀{Γ₁ Γ₂ p q}
               → Deduction Γ₁ p
               → Deduction Γ₂ q
               → Deduction (Γ₁ ++ Γ₂) (p ∧ q)

  ConjElim   : ∀{Γ₁ Γ₂ p q r}
               → Deduction Γ₁ (p ∧ q)
               → Deduction Γ₂ r
               → Deduction (Γ₁ ++ (Γ₂ ∖ p ∖ q)) r

  DisjIntro₁ : ∀{Γ p}
               → Deduction Γ p
               → (q : Formula)
               → Deduction Γ (p ∨ q)

  DisjIntro₂ : ∀{Γ p}
               → Deduction Γ p
               → (q : Formula)
               → Deduction Γ (q ∨ p)

  DisjElim   : ∀{Γ₁ Γ₂ Γ₃ p q r}
               → Deduction Γ₁ (p ∨ q)
               → Deduction Γ₂ r
               → Deduction Γ₃ r
               → Deduction (Γ₁ ++ (Γ₂ ∖ p) ++ (Γ₃ ∖ q)) r

  UniGIntro  : ∀{Γ p x}
               → (x NotFreeIn Γ)
               → Deduction Γ p
               → (x : Term)
               → Deduction Γ (Α x p)

  UniGElim   : ∀{Γ p x}
               → (y : Term)
               → Deduction Γ (Α x p)
               → Deduction Γ (rename p x y)

  ExiGIntro  : ∀{Γ p}
               → Deduction Γ p
               → (x : Term)
               → Deduction Γ (Ε x p)

  ExiGElim   : ∀{Γ₁ Γ₂ p q x}
               → (y : Term)
               → y NotFreeIn [ q ]
               → Deduction Γ₁ (Ε x p)
               → Deduction Γ₂ q
               → y NotFreeIn (Γ₂ ∖ (rename p x y))
               → Deduction (Γ₁ ++ (Γ₂ ∖ (rename p x y))) q



Conclusion : {p : Formula} → {Γ : List Formula} → Deduction Γ p → Formula
Conclusion {p} _ = p

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
test4 = ConjElim (Assume (P ∧ Q)) (Assume P)

test5 : Deduction [ P ∧ Q ] Q
test5 = ConjElim (Assume (P ∧ Q)) (Assume Q)

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
test10 = UniGIntro test10terms (ConjElim (UniGElim X (Assume (Α X (S X ∧ P)))) (Assume (S X))) X

test11 : Deduction [ (Α X (S X)) ] (S Y)
test11 = UniGElim Y (Assume (Α X (S X)))

test12 : Deduction [ S X ] (Ε X (S X))
test12 = ExiGIntro (Assume (S X)) X

test13 : Deduction ((Ε X (S X)) :: [ Α X ((S X) ⇒ P) ]) P
test13 = ExiGElim Y (Recur AllClosed) (Assume (Ε X (S X))) (ArrowElim (UniGElim Y (Assume (Α X ((S X) ⇒ P)))) (Assume (S Y))) (Recur AllClosed)



-- Non-trivial usage

all-contradict : Deduction ((¬(S X)) :: [ Α X (S X) ]) ⊥
all-contradict = ArrowElim (Assume (¬(S X))) (UniGElim X (Assume (Α X (S X))))


not-for-all : Deduction [ (¬(S X)) ] ( ¬ (Α X (S X)))
not-for-all = ArrowIntro all-contradict (Α X (S X))


gmp-complement : Deduction [ Ε X (¬ (S X)) ] (¬(Α X (S X)))
gmp-complement = ExiGElim X (Recur AllClosed) (Assume (Ε X (¬(S X)))) not-for-all AllClosed




