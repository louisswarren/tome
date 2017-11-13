open import common
open import deduction
open import formula
open import texify

X Y : Term
X = term "x"
Y = term "y"

Φ : Formula
Φ = atom "\\Phi"

P : Term → Formula
P = pred "P"

∀x = Α X
∃x = Ε X
∀y = Α Y
∃y = Ε Y

-- Macros

assume-and-elim : (p q : Formula) → Deduction (p ⇒ q :: [ p ]) q
assume-and-elim p q = ArrowElim (Assume (p ⇒ q)) (Assume p)


⇒id : (p : Formula) → Deduction _ (p ⇒ p)
⇒id p = ArrowIntro (Assume p) p


record Scheme : Set where
  field
    formula : Formula
    name    : String


-- Results

hε  = ∃y(∃x(P X) ⇒ (P Y))
hε' = (Φ ⇒ ∃x(P X)) ⇒ ∃x(Φ ⇒ P X)
hε'-trivial = replace Φ (∃x(P X)) hε'


hε-equiv₁ : Deduction [ hε ] hε'
hε-equiv₁ = ArrowIntro (ExistElim X (Assume hε) (ExistIntro (ArrowIntro
            (ArrowElim (Assume (Ε X (P X) ⇒ P X))
            (assume-and-elim Φ (Ε X (P X)))) Φ) X))
                 (Φ ⇒ Ε X (P X))

hε-equiv₂ : Deduction [ hε'-trivial ] hε
hε-equiv₂ = ExistElim Y (ArrowElim (Assume hε'-trivial) (⇒id (Ε X (P X))))
                        (ExistIntro (Assume (Ε X (P X) ⇒ P Y)) Y)
