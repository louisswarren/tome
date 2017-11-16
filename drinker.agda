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
Px = P X
¬Px = ¬ Px

∀y = Α Y
∃y = Ε Y
Py = P Y
¬Py = ¬ Py


¬∀x ¬∃x ¬∀y ¬∃y : Formula → Formula
¬∀x Φ = ¬ (∀x Φ)
¬∃x Φ = ¬ (∃x Φ)
¬∀y Φ = ¬ (∀y Φ)
¬∃y Φ = ¬ (∃y Φ)


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

hε  = ∃y(∃x Px ⇒ Py)
hε' = (Φ ⇒ ∃x Px) ⇒ ∃x(Φ ⇒ Px)
hε'-trivial = replace Φ (∃x Px) hε'


hε-equiv₁ : Deduction [ hε ] hε'
hε-equiv₁ = ArrowIntro (ExistElim X (Assume hε) (ExistIntro X (ArrowIntro
            (ArrowElim (Assume (∃x Px ⇒ Px))
            (assume-and-elim Φ (∃x Px))) Φ)))
                 (Φ ⇒ ∃x Px)

hε-equiv₂ : Deduction [ hε'-trivial ] hε
hε-equiv₂ = ExistElim Y (ArrowElim (Assume hε'-trivial) (⇒id (∃x Px)))
                        (ExistIntro Y (Assume (∃x Px ⇒ Py)))


LEM : Formula → Formula
LEM Φ = Φ ∨ (¬ Φ)

dp  = ∃y(Py ⇒ ∀x Px)
dp' = ∃y(∀x (Py ⇒ Px))
gmp = ¬ (∀x Px) ⇒ ∃x (¬ Px)

lem-class : (p : Formula) → Proof _ (LEM p)
lem-class p = classicalproof "LEM" (ClassAbsurd (LEM p) (ArrowElim
              (ArrowIntro (ArrowElim (Assume (¬ (LEM p)))
                           (DisjIntro₂ (Assume (¬ p)) p)) (¬ p))
              (ArrowIntro (ArrowElim (Assume (¬ (LEM p)))
                           (DisjIntro₁ (Assume p) (¬ p))) p)))

tex-lem = texifypf (lem-class Φ)

gmp-class : Proof [] gmp
gmp-class = classicalproof "GMP"
            (ArrowIntro (ClassAbsurd (∃x ¬Px)
             (ArrowElim (Assume (¬∀x Px)) (UnivIntro X
              (ClassAbsurd Px (ArrowElim (Assume (¬∃x ¬Px))
               (ExistIntro X (Assume ¬Px)))))))
             (¬∀x Px))

dp-class : Deduction [] dp
dp-class = DisjElim (Cite (lem-class (∀x Px)))
            (ExistIntro Y (ArrowIntro (Assume (∀x Px)) Py))
            (ExistElim Y (ArrowElim (Cite gmp-class) (Assume (¬∀x Px)))
             (ExistIntro Y (ArrowIntro (IntAbsurd (∀x Px)
                                (ArrowElim (Assume ¬Py) (Assume Py))) Py)))

dp-equiv₁ : Deduction [ dp ] dp'
dp-equiv₁ = (ExistElim Y (Assume dp) (ExistIntro Y
             (UnivIntro X (ArrowIntro (UnivElim X
              (ArrowElim (Assume (Py ⇒ ∀x Px)) (Assume Py))) Py))))

dp-equiv₂ : Deduction [ dp' ] dp
dp-equiv₂ = ExistElim Y (Assume dp') (ExistIntro Y
             (ArrowIntro (UnivIntro X
              (ArrowElim (UnivElim X (Assume (∀x (Py ⇒ Px)))) (Assume Py))) Py))

