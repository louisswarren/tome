open import common
open import formula
open import deduction
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
replaceall α β = map (replace α β)


-- This will fail to typecheck if the translation does not have a valid proof.
-- Should only happen if you do something wrong.
translate : ∀{Γ p}
          → (α : Formula)
          → (β : Formula)
          → Deduction Γ p
          → Deduction (replaceall α β Γ) (replace α β p)

translate α β (Assume p) = Assume (replace α β p)
translate α β (ArrowIntro T p) = ArrowIntro (translate α β T) (p)
translate α β (ArrowElim T₁ T₂) = ArrowElim (translate α β T₁) (translate α β T₂)
translate α β (ConjIntro T₁ T₂) = ConjIntro (translate α β T₁) (translate α β T₂)
translate α β (ConjElim  T₁ T₂) = ConjElim  (translate α β T₁) (translate α β T₂)
translate α β (DisjIntro₁ T p) = DisjIntro₁ (translate α β T) (replace α β p)
translate α β (DisjIntro₂ T p) = DisjIntro₂ (translate α β T) (replace α β p)
translate α β (DisjElim T₁ T₂ T₃) = DisjElim (translate α β T₁)
                                             (translate α β T₂) (translate α β T₃)
translate α β 
translate α β 
