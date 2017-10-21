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
               → Deduction Γ q
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
               → x NotFreeIn Γ
               → Deduction Γ p
               → (x : Term)
               → Deduction Γ (Α x p)

  UniGElim   : ∀{Γ p x}
               → (y : Term)
               → Deduction Γ (Α x p)
               → Deduction Γ (p [ x / y ])

  ExiGIntro  : ∀{Γ p}
               → Deduction Γ p
               → (x : Term)
               → Deduction Γ (Ε x p)

  ExiGElim   : ∀{Γ₁ Γ₂ p q x}
               → (y : Term)
               → {_ : isTrue (not (y freein q))}
               → Deduction Γ₁ (Ε x p)
               → Deduction Γ₂ q
               → y NotFreeIn (Γ₂ ∖ (p [ x / y ]))
               → Deduction (Γ₁ ++ (Γ₂ ∖ (p [ x / y ]))) q

conclusion : ∀{p Γ} → Deduction Γ p → Formula
conclusion {p} _ = p

----------------------------------------


texformula : Formula → String
texsubformula : Formula → String

texformula (atom n) = n
texformula (pred n (term t)) = n >> t
texformula (p ⇒ q) = (texsubformula p) >> " \\mimp " >> (texsubformula q)
texformula (p ∧ q) = (texsubformula p) >> " \\mand " >> (texsubformula q)
texformula (p ∨ q) = (texsubformula p) >> " \\mor " >> (texsubformula q)
texformula (Α (term t) p) = "\\forall_{" >> t >> "}" >> (texsubformula p)
texformula (Ε (term t) p) = "\\exists_{" >> t >> "}" >> (texsubformula p)

texsubformula f@(atom n) = texformula f
texsubformula f@(pred n t) = texformula f
texsubformula f@(Α _ _)    = texformula f
texsubformula f@(Ε _ _)    = texformula f
texsubformula p          = "(" >> texformula p >> ")"

texroot : ∀{Γ p} → ℕ → Deduction Γ p → String → String
texroot 1 T rule = "\\RightLabel{" >> rule >> "}\n" >>
                   "\\UnaryInfC{$" >> texformula (conclusion T) >> "$}\n"
texroot 2 T rule = "\\RightLabel{" >> rule >> "}\n" >>
                   "\\BinaryInfC{$" >> texformula (conclusion T) >> "$}\n"
texroot 3 T rule = "\\RightLabel{" >> rule >> "}\n" >>
                   "\\TernaryInfC{$" >> texformula (conclusion T) >> "$}\n"
texroot _ T rule = ""



texify : ∀{Γ p} → Deduction Γ p → String
texify d@(Assume _)           = "\\AxiomC{$" >> texformula (conclusion d) >> "$}\n"
texify d@(ArrowIntro T _)     = (texify T) >> texroot 1 d "\\ndii"
texify d@(ArrowElim T₁ T₂)    = (texify T₁) >> (texify T₂) >> texroot 2 d "\\ndie"
texify d@(ConjIntro T₁ T₂)    = (texify T₁) >> (texify T₂) >> texroot 2 d "\\ndci"
texify d@(ConjElim T₁ T₂)     = (texify T₁) >> (texify T₂) >> texroot 2 d "\\ndce"
texify d@(DisjIntro₁ T _)     = (texify T) >> texroot 1 d "\\nddi"
texify d@(DisjIntro₂ T _)     = (texify T) >> texroot 1 d "\\nddi"
texify d@(DisjElim T₁ T₂ T₃)  = (texify T₁) >> (texify T₂) >> (texify T₃) >> texroot 2 d "\\ndce"
texify d@(UniGIntro _ T _)    = (texify T) >> texroot 1 d "\\ndfi"
texify d@(UniGElim _ T)       = (texify T) >> texroot 1 d "\\ndfe"
texify d@(ExiGIntro T _)      = (texify T) >> texroot 1 d "\\ndei"
texify d@(ExiGElim _ T₁ T₂ _) = (texify T₁) >> (texify T₂) >> texroot 2 d "\\ndee"


----------------------------------------

X Y Z : Term
X = term "x"
Y = term "y"
Z = term "z"

⊥ P Q R : Formula
⊥ = atom "\\bot"
P = atom "P"
Q = atom "Q"
R = atom "R"

S : Term → Formula
S = pred "S"

¬ : Formula → Formula
¬ a = a ⇒ ⊥


----------------------------------------

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
test13 = ExiGElim Y (Assume (Ε X (S X))) (ArrowElim (UniGElim Y (Assume (Α X ((S X) ⇒ P)))) (Assume (S Y))) (Recur AllClosed)

test14terms : Y NotFreeIn [ Α X (S X) ]
test14terms = Recur AllClosed

test14 : Deduction [ Α X (S X) ] (Α Y (S Y))
test14 = UniGIntro test14terms (UniGElim Y (Assume (Α X (S X)))) Y

test15 : Deduction [ Ε X (S X) ] (Ε Y (S Y))
test15 = ExiGElim Y (Assume (Ε X (S X))) (ExiGIntro (Assume (S Y)) Y) AllClosed

-- Non-trivial usage

all-contradict : Deduction ((¬(S X)) :: [ Α X (S X) ]) ⊥
all-contradict = ArrowElim (Assume (¬(S X))) (UniGElim X (Assume (Α X (S X))))


not-for-all : Deduction [ (¬(S X)) ] ( ¬ (Α X (S X)))
not-for-all = ArrowIntro all-contradict (Α X (S X))


gmp-complement : Deduction [ Ε X (¬ (S X)) ] (¬(Α X (S X)))
gmp-complement = ExiGElim X (Assume (Ε X (¬(S X)))) not-for-all AllClosed

nd : String
nd = texify gmp-complement
