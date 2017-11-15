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

∀y = Α Y
∃y = Ε Y
Py = P Y

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

s = texify hε-equiv₁


LEM : Formula → Formula
LEM Φ = Φ ∨ (¬ Φ)

EFQ : Formula → Formula
EFQ Φ = ⊥ ⇒ Φ

dp  = ∃y(Py ⇒ ∀x Px)
gmp = ¬ (∀x Px) ⇒ ∃x (¬ Px)

postulate
  gmp-deduction : Deduction [] gmp

gmp-proof = proof "GMP" gmp-deduction

dp-class : Deduction (LEM (∀x Px) :: gmp :: EFQ (∀x Px) :: []) dp
dp-class = DisjElim (Assume (LEM (∀x Px)))
            (ExistIntro Y (ArrowIntro (Assume (∀x Px)) Py))
            (ExistElim Y (ArrowElim (Assume gmp) (Assume (¬ (∀x Px))))
             (ExistIntro Y (ArrowIntro (ArrowElim (Assume (EFQ (∀x Px)))
                                (ArrowElim (Assume (¬ Py)) (Assume Py))) Py)))
