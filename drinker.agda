open import common
open import deduction
open import formula
open import texify

X Y : Term
X = term "x"
Y = term "y"

P : Term → Formula
P = pred "P"

Q : Formula
Q = atom "Q"

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

-- Propositional unary schemes
LEM WLEM : Formula → Formula
DGP      : Formula → Formula → Formula

LEM  Φ   = Φ ∨ (¬ Φ)
WLEM Φ   = (¬ Φ) ∨ (¬¬ Φ)
DGP  Φ Ψ = Φ ⇒ Ψ ∨ Ψ ⇒ Φ


-- First-order schemes
DP Hε GMP : (Term → Formula) → Formula
IP       : (α : Formula) → (Term → Formula) → (t : Term) → {_ : t notfreein [ α ]} → Formula

DP    A = ∃y((A Y) ⇒ ∀x (A X))
Hε    A = ∃y(∃x (A X) ⇒ A Y)
IP  N A t = (N ⇒ Ε t (A X)) ⇒ Ε t (N ⇒ (A X))
GMP   A = ¬∀x (A X) ⇒ ∃x (¬(A X))

-- Canonical instances
hε  = Hε P
hε' = ∃y(∀x (Py ⇒ Px))
ip  = IP Q P X
dp  = DP P
dp' = ∃y(∀x (Py ⇒ Px))
gmp = GMP P



-- Example: Proving canonical instances

hε-equiv₁ : Proof [ Hε P ] ip
hε-equiv₁ = minimalproof "Hε ⊢ IP"
            (ArrowIntro (ExistElim X (Assume (Hε P)) (ExistIntro X (ArrowIntro
             (ArrowElim (Assume (∃x Px ⇒ Px))
             (assume-and-elim Q (∃x Px))) Q)))
             (Q ⇒ ∃x Px))

hε-equiv₂ : Proof [ IP (∃x Px) P X ] hε
hε-equiv₂ = minimalproof "IP ⊢ Hε"
            (ExistElim Y (ArrowElim (Assume (IP (∃x Px) P X)) (⇒id (∃x Px)))
                         (ExistIntro Y (Assume (∃x Px ⇒ Py))))


-- Example: Proving a scheme

lem-class : (p : Formula) → Proof _ (LEM p)
lem-class p = classicalproof "LEM" (ClassAbsurd (LEM p) (ArrowElim
              (ArrowIntro (ArrowElim (Assume (¬ (LEM p)))
                           (DisjIntro₂ (Assume (¬ p)) p)) (¬ p))
              (ArrowIntro (ArrowElim (Assume (¬ (LEM p)))
                           (DisjIntro₁ (Assume p) (¬ p))) p)))

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

