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

s = texify hε-equiv₁


LEM : Formula → Formula
LEM Φ = Φ ∨ (¬ Φ)

EFQ : Formula → Formula
EFQ Φ = ⊥ ⇒ Φ

DNE : Formula → Formula
DNE Φ = (¬¬ Φ) ⇒ Φ

DNEpred : Term → Formula → Formula
DNEpred X Φ = Α X ((¬¬ Φ) ⇒ Φ)

dp  = ∃y(Py ⇒ ∀x Px)
dp' = ∃y(∀x (Py ⇒ Px))
gmp = ¬ (∀x Px) ⇒ ∃x (¬ Px)


gmp-deduction : Deduction (DNE (∃x ¬Px) :: DNEpred X Px :: []) gmp
gmp-deduction = ArrowIntro (ArrowElim (Assume (DNE (∃x ¬Px)))
                 (ArrowIntro
                  (ArrowElim (Assume (¬∀x Px))
                   (UnivIntro X (ArrowElim (
                                 (UnivElim X (Assume (DNEpred X Px))))
                    (ArrowIntro (ArrowElim (Assume (¬∃x ¬Px))
                     (ExistIntro X (Assume ¬Px))) ¬Px))))
                  (¬∃x ¬Px)))
                 (¬∀x Px)


gmp-proof = proof "GMP" gmp-deduction

dp-class : Deduction (LEM (∀x Px) :: gmp :: EFQ (∀x Px) :: []) dp
dp-class = DisjElim (Assume (LEM (∀x Px)))
            (ExistIntro Y (ArrowIntro (Assume (∀x Px)) Py))
            (ExistElim Y (ArrowElim (Assume gmp) (Assume (¬∀x Px)))
             (ExistIntro Y (ArrowIntro (ArrowElim (Assume (EFQ (∀x Px)))
                                (ArrowElim (Assume ¬Py) (Assume Py))) Py)))

dp-equiv₁ : Deduction [ dp ] dp'
dp-equiv₁ = (ExistElim Y (Assume dp) (ExistIntro Y
             (UnivIntro X (ArrowIntro (UnivElim X
              (ArrowElim (Assume (Py ⇒ ∀x Px)) (Assume Py))) Py))))

dp-equiv₂ : Deduction [ dp' ] dp
dp-equiv₂ = ExistElim Y (Assume dp') (ExistIntro Y
             (ArrowIntro (UnivIntro X
              (ArrowElim (UnivElim X (Assume (∀x (Py ⇒ Px)))) (Assume Py))) Py))

