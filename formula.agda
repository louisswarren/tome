open import common

module formula where

data Term : Set where
  term : String → Term

TermEq : Term → Term → Bool
TermEq (term n) (term m) = n === m


----------------------------------------

data Formula : Set where
  atom  : String → Formula
  pred  : String → Term → Formula
  _⇒_   : Formula → Formula → Formula
  _∧_   : Formula → Formula → Formula
  _∨_   : Formula → Formula → Formula
  Α     : Term → Formula → Formula
  Ε     : Term → Formula → Formula


infixr 110 _∨_
infixr 120 _∧_
infixr 130 _⇒_

⊥ = atom "\\bot"

¬ : Formula → Formula
¬ a = a ⇒ ⊥

¬¬ : Formula → Formula
¬¬ a = ¬ (¬ a)

_[_/_] : Formula → Term → Term → Formula
(atom n)[ _ / _ ]   = atom n
(pred n t)[ x / y ] with (TermEq t x)
...                            | true  = (pred n y)
...                            | false = (pred n t)
(a ⇒ b)[ x / y ]    = (a [ x / y ]) ⇒ (b [ x / y ])
(a ∧ b)[ x / y ]    = (a [ x / y ]) ∧ (b [ x / y ])
(a ∨ b)[ x / y ]    = (a [ x / y ]) ∨ (b [ x / y ])
(Α t f)[ x / y ]    with (TermEq t x)
...                    | true  = Α t f
...                    | false = Α t (f [ x / y ])
(Ε t f)[ x / y ]    with (TermEq t x)
...                    | true  = Ε t f
...                    | false = Ε t (f [ x / y ])


_≡_ : Formula → Formula → Bool
(atom n) ≡ (atom m)     = n === m
(pred n t) ≡ (pred m s) = (n === m) and TermEq t s
(a ⇒ b) ≡ (c ⇒ d)       = (a ≡ c) and (b ≡ d)
(a ∧ b) ≡ (c ∧ d)       = (a ≡ c) and (b ≡ d)
(a ∨ b) ≡ (c ∨ d)       = (a ≡ c) and (b ≡ d)
(Α t f) ≡ (Α s g)       = (f [ t / s ]) ≡ g
(Ε t f) ≡ (Ε s g)       = (f [ t / s ]) ≡ g
_ ≡ _                   = false


_∖_ : List Formula → Formula → List Formula
[] ∖ _        = []
(x :: xs) ∖ y with (x ≡ y)
...              | true  = (xs ∖ y)
...              | false = x :: (xs ∖ y)

infixl 200 _∖_


_freein_ : Term → Formula → Bool
t freein (atom _)   = false
t freein (pred _ s) = (TermEq t s)
t freein (a ⇒ b)    = (t freein a) or (t freein b)
t freein (a ∧ b)    = (t freein a) or (t freein b)
t freein (a ∨ b)    = (t freein a) or (t freein b)
t freein (Ε n a)    = (not (TermEq t n)) and (t freein a)
t freein (Α n a)    = (not (TermEq t n)) and (t freein a)


_notfreein_ : Term → List Formula → Set
t notfreein Γ = isTrue (not (any (_freein_ t) Γ))


_∈_ : Formula → List Formula → Bool
x ∈ []        = false
x ∈ (y :: ys) = (x ≡ y) or (x ∈ ys)



-- Replace one atom with a formula, one predicate with another (keeping
-- quantifier in place), or otherwise leave it as-is.
replace : Formula → Formula → Formula → Formula
replace (atom n)   q f@(atom m)   with (n === m)
...                                | true  = q
...                                | false = f
replace (atom _)   _ f@(pred _ _) = f
replace (pred _ _) _ f@(atom _)   = f
replace (pred n _) q f@(pred m _) with (n === m)
...                                | true  = q
...                                | false = f
replace α β (r ⇒ s) = (replace α β r) ⇒ (replace α β s)
replace α β (r ∧ s) = (replace α β r) ∧ (replace α β s)
replace α β (r ∨ s) = (replace α β r) ∨ (replace α β s)
replace α β (Α t r) = Α t (replace α β r)
replace α β (Ε t r) = Ε t (replace α β r)
replace _ _ f       = f

replaceall : Formula → Formula → List Formula → List Formula
replaceall α β x = map (replace α β) x

