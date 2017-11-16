open import common
open import formula
open import deduction
open import scheme
open import texify

----------------------------------------

X Y Z : Term
X = term "x"
Y = term "y"
Z = term "z"

P Q R : Formula
P = atom "P"
Q = atom "Q"
R = atom "R"

S : Term → Formula
S = pred "S"

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

test10 : Deduction [ (Α X (S X ∧ P)) ] (Α X (S X))
test10 = UnivIntro X (ConjElim (UnivElim X (Assume (Α X (S X ∧ P)))) (Assume (S X)))

test11 : Deduction [ (Α X (S X)) ] (S Y)
test11 = UnivElim Y (Assume (Α X (S X)))

test12 : Deduction [ S X ] (Ε X (S X))
test12 = ExistIntro X (Assume (S X))

test13 : Deduction ((Ε X (S X)) :: [ Α X ((S X) ⇒ P) ]) P
test13 = ExistElim Y (Assume (Ε X (S X))) (ArrowElim (UnivElim Y (Assume (Α X ((S X) ⇒ P)))) (Assume (S Y)))

test14 : Deduction [ Α X (S X) ] (Α Y (S Y))
test14 = UnivIntro Y (UnivElim Y (Assume (Α X (S X))))

test15 : Deduction [ Ε X (S X) ] (Ε Y (S Y))
test15 = ExistElim Y (Assume (Ε X (S X))) (ExistIntro Y (Assume (S Y)))

-- Non-trivial usage

dneg : Deduction [ P ] (¬¬ P)
dneg = ArrowIntro (ArrowElim (Assume (¬ P)) (Assume P)) (¬ P)

wlemded : Deduction [ P ∨ ¬ P ] ((¬ P) ∨ (¬¬ P))
wlemded = DisjElim (Assume (P ∨ ¬ P)) (DisjIntro₂ dneg (¬ P))
                                   (DisjIntro₁ (Assume (¬ P)) (¬¬ P))


all-contradict : Deduction ((¬(S X)) :: [ Α X (S X) ]) ⊥
all-contradict = ArrowElim (Assume (¬(S X))) (UnivElim X (Assume (Α X (S X))))


not-for-all : Deduction [ (¬(S X)) ] ( ¬ (Α X (S X)))
not-for-all = ArrowIntro all-contradict (Α X (S X))


gmp-complement : Deduction [ Ε X (¬ (S X)) ] (¬(Α X (S X)))
gmp-complement = ExistElim X (Assume (Ε X (¬(S X)))) not-for-all

nd : String
nd = texify gmp-complement


tex1 : String
tex1 = texformula ((P ∨ Q) ⇒ ⊥)

tex2 : String
tex2 = texformula (((P ∨ Q) ⇒ ⊥) ∧ R)

tex3 : String
tex3 = texformula ((P ⇒ ⊥) ∧ R)


tex1' : String
tex1' = texformula ((P ∨ Q) ⇒ P)

tex2' : String
tex2' = texformula (((P ∨ Q) ⇒ P) ∧ R)

tex3' : String
tex3' = texformula ((P ⇒ P) ∧ R)






-- A scheme-level derivation allows arbitrary instantiation inside a deduction


findpreds : Formula → List Formula
findpreds p@(atom _)   with (p ≡ ⊥)
...                        | true  = []
...                        | false = p :: []
findpreds p@(pred _ _) = [ p ]
findpreds (p ⇒ q)      = (findpreds p) ++ (findpreds q)
findpreds (p ∧ q)      = (findpreds p) ++ (findpreds q)
findpreds (p ∨ q)      = (findpreds p) ++ (findpreds q)
findpreds (Α _ p)      = findpreds p
findpreds (Ε _ p)      = findpreds p


lem = P ∨ ¬ P
wlem = ¬ P ∨ ¬¬ P

-- wlempf : Proof [] wlem
-- wlempf = Using (lem) P (¬ P) (Generalise (Assume wlem))





-- Contraposition as a function
contraposfunc : ∀{Γ p q} → Deduction Γ (p ⇒ q) → Deduction _ ((¬ q) ⇒ (¬ p))
contraposfunc {_} {p} {q} T =
  ArrowIntro (ArrowIntro (ArrowElim (Assume (¬ q))
                                     (ArrowElim T (Assume p))) p) (¬ q)

contrapospf : Proof [ P ⇒ Q ] ((¬ Q) ⇒ (¬ P))
contrapospf = minimalproof "Contraposition" (contraposfunc (Assume (P ⇒ Q)))

sd1 : Deduction [ P ⇒ Q ∨ Q ⇒ P ] ((¬ Q) ⇒ (¬ P) ∨ Q ⇒ P)
sd1 = DisjElim (Assume (P ⇒ Q ∨ Q ⇒ P))
                (DisjIntro₁ (contraposfunc (Assume (P ⇒ Q))) (Q ⇒ P))
                (DisjIntro₂ (Assume (Q ⇒ P)) (¬ Q ⇒ ¬ P))

--sd2 : Deduction [ P ⇒ Q ∨ Q ⇒ P ] ((¬ Q) ⇒ (¬ P) ∨ Q ⇒ P)
--sd2 = DisjElim (Assume (P ⇒ Q ∨ Q ⇒ P))
--                (DisjIntro₁ (Collapse ((Assume (P ⇒ Q)) :: []) contrapospf)
--                            (Q ⇒ P))
--                (DisjIntro₂ (Assume (Q ⇒ P)) (¬ Q ⇒ ¬ P))



