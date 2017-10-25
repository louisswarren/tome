open import common
open import formula
open import deduction
open import texify

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
