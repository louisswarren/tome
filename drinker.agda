open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Deduction
open import Formula
open import Texify

open import common
open import sugar

-- Without loss of generality, assume that schemes are applied only to formulae
-- in which the schemes' quantifiers are not free.

EFQ LEM WLEM DGP GLPO GLPOA GMP WGMP DP HE DPN HEN DNSU DNSE UD IP : Scheme
FIN∀ FIN∃ : Scheme


efq : Formula → Formula
efq Φ = ⊥ ⇒ Φ

EFQ = unaryscheme "EFQ" efq


lem wlem : Formula → Formula
lem  Φ = Φ ∨ ¬ Φ
wlem Φ = ¬ Φ ∨ ¬¬ Φ

LEM  = unaryscheme "LEM" lem
WLEM = unaryscheme "WLEM" wlem



dgp : Formula → Formula → Formula
dgp Φ Ψ  = (Φ ⇒ Ψ) ∨ (Ψ ⇒ Φ)

DGP = binaryscheme "DGP" dgp



glpo glpoa gmp wgmp : Formula → Formula
glpo  Φx = ∀x ¬Φx ∨ ∃x Φx                                       where ¬Φx = ¬ Φx
glpoa Φx = ∀x Φx ∨ ∃x ¬Φx                                       where ¬Φx = ¬ Φx
gmp   Φx = ¬∀x Φx ⇒ ∃x ¬Φx                                      where ¬Φx = ¬ Φx
wgmp  Φx = ¬∀x Φx ⇒ ¬¬(∃x ¬Φx)                                  where ¬Φx = ¬ Φx

GLPO  = unaryscheme "GLPO"  glpo
GLPOA = unaryscheme "GLPOA" glpoa
GMP   = unaryscheme "GMP"   gmp
WGMP  = unaryscheme "WGMP"  wgmp



dp he dpn hen : Formula → Formula
dp  Φx = ∃y(Φy ⇒ ∀x Φx)                                  where Φy = Φx [ x / y ]
he  Φx = ∃y(∃x Φx ⇒ Φy)                                  where Φy = Φx [ x / y ]
dpn Φx = dp (¬ Φx)
hen Φx = he (¬ Φx)

DP  = unaryscheme "DP"  dp
HE  = unaryscheme "HE"  he
DPN = unaryscheme "DPN" dpn
HEN = unaryscheme "HEN" hen



dnsu dnse : Formula → Formula
dnsu Φx = ∀x(¬¬ Φx) ⇒ ¬¬(∀x Φx)
dnse Φx = ¬¬(∃x Φx) ⇒ ∃x (¬¬ Φx)

DNSU = unaryscheme "DNSU" dnsu
DNSE = unaryscheme "DNSE" dnse



ud ip : Formula → Formula → Formula
ud Φx Ψ = ∀x (Φx ∨ Ψ) ⇒ (∀x Φx ∨ Ψ)
ip Φx Ψ = (Ψ ⇒ ∃x Φx) ⇒ ∃x(Ψ ⇒ Φx)

UD = binaryscheme "UD" ud
IP = binaryscheme "IP" ip




A = atom (mkprop "A") []
B = atom (mkprop "B") []
P : Term → Formula
P t = atom (mkrel 1 "P") (t ∷ [])

Px = P x
Py = P y
Pz = P z

¬A = ¬ A
¬B = ¬ B
¬Px = ¬ Px
¬Py = ¬ Py
¬Pz = ¬ Pz

¬¬A = ¬¬ A
¬¬B = ¬¬ B
¬¬Px = ¬¬ Px
¬¬Py = ¬¬ Py
¬¬Pz = ¬¬ Pz


-- Semantically, at least one term exists. Giving two names for terms does not
-- assert that these terms are actually different.
t⁰ = functerm (mkconst "0") []
t¹ = functerm (mkconst "1") []


-- For these terms to be different, there must be a predicate which
-- distinguishes them.
D : Term → Formula
D t = atom (mkrel 1 "D") (t ∷ [])
Dt⁰ = D t⁰
Dt¹ = D t¹
¬Dt¹ = ¬ Dt¹
Dx  = D x
¬Dx = ¬ Dx
Dy  = D y
¬Dy = ¬ Dy
[TT] : List Scheme
[TT] = nullaryscheme "D0" (Dt⁰)
     ∷ nullaryscheme "$\\Tneg{D1}$" (¬Dt¹)
     ∷ nullaryscheme "D" (∀x (D x ∨ ¬ (D x)))
     ∷ []


-- Use this to apply predicative schemes to propositional problems
fin∀ fin∃ : Formula → Formula → Formula
fin∀ Φ Ψ = ∀x ((Dx ⇒ Φ) ∧ (¬Dx ⇒ Ψ)) ⇒ (Φ ∧ Ψ)
FIN∀ = binaryscheme "FIN$\\forall$" fin∀

fin∃ Φ Ψ = ∃x ((Dx ⇒ Φ) ∧ (¬Dx ⇒ Ψ)) ⇒ (Φ ∨ Ψ)
FIN∃ = binaryscheme "FIN$\\exists$" fin∃


tt-fin∀ : [TT] ⊃ (fin∀ A B)
tt-fin∀ = arrowintro (∀x ((Dx ⇒ A) ∧ (¬Dx ⇒ B)))
           (conjintro
            (arrowelim
             (conjelim
              (univelim t⁰ (assume (∀x ((Dx ⇒ A) ∧ (¬Dx ⇒ B)))))
              (assume (Dt⁰ ⇒ A)))
             (axiom 0 []))
            (arrowelim
             (conjelim
              (univelim t¹ (assume (∀x ((Dx ⇒ A) ∧ (¬Dx ⇒ B)))))
              (assume (¬Dt¹ ⇒ B)))
             (axiom 1 [])))

tt-fin∃ : [TT] ⊃ (fin∃ A B)
tt-fin∃ = arrowintro (∃x ((Dx ⇒ A) ∧ (¬Dx ⇒ B)))
           (existelim (assume (∃x ((Dx ⇒ A) ∧ (¬Dx ⇒ B))))
            (conjelim (assume ((Dx ⇒ A) ∧ (¬Dx ⇒ B)))
             (disjelim
              (univelim x (axiom 2 []))
              (disjintro₁ B (arrowelim (assume (Dx ⇒ A)) (assume Dx)))
              (disjintro₂ A (arrowelim (assume (¬Dx ⇒ B)) (assume ¬Dx))))))

[FIN] : List Scheme
[FIN] = FIN∀ ∷ FIN∃ ∷ []

-- Lemmae and macros

-- A macro cannot (with the current system) be proved discharge assumptions in
-- general, but when applied, Agda can prove its effect for a given case
macro-dni : ∀{α Ω Γ} → Ω , Γ ⊢ α → Ω , _ ⊢ (¬¬ α)
macro-dni {α} T = arrowintro (¬ α) (arrowelim (assume (¬ α)) T)

macro-efq-helper : ∀{ω Ω Γ} → ∀ α → ω ∷ EFQ ∷ Ω , Γ ⊢ ⊥ → ω ∷ EFQ ∷ Ω , Γ ⊢ α
macro-efq-helper α T = arrowelim (axiom 1 (α ∷ [])) T

-- macro-contra : ∀{α β Ω Γ} → Ω , Γ ⊢ α ⇒ β → Ω , _ ⊢ (¬ β) ⇒ (¬ α)
-- macro-contra {α} {β} T = arrowintro (¬ β) (arrowintro α
--                           (arrowelim (assume (¬ β)) (arrowelim T (assume α))))
--
-- macro-tollens : ∀{α β Ω Γ₁ Γ₂} → Ω , Γ₁ ⊢ α ⇒ β → Ω , Γ₂ ⊢ ¬ β → Ω , _ ⊢ ¬ α
-- macro-tollens {α} {β} T₁ T₂ = arrowintro α (arrowelim T₂
--                               (arrowelim T₁ (assume α)))
--
-- macro-incons : ∀{α β Ω Γ₁ Γ₂ Γ₃}
--                → Ω , Γ₁ ⊢ α ⇒ β
--                → Ω , Γ₂ ⊢ ¬ β
--                → Ω , Γ₃  ⊢ α
--                → Ω , Γ₂ ++ Γ₁ ++ Γ₃ ⊢ ⊥
-- macro-incons {α} {β} T₁ T₂ T₃ = arrowelim T₂ (arrowelim T₁ T₃)
--
--
-- macro-tne : ∀{α Ω Γ} → Ω , Γ ⊢ ¬¬(¬ α) → Ω , _ ⊢ ¬ α
-- macro-tne {α} T = arrowintro α (arrowelim T (macro-dni (assume α)))
--
-- Didn't need to prove this
--lemma01 : ⊢ (¬∃x ¬¬Px ⇒ (∃x ¬Px))
--lemma01 = arrowintro (¬∃x ¬¬Px) (existintro x xvar
--           (arrowintro Px (arrowelim (assume (¬∃x ¬¬Px))
--            (existintro x xvar (macro-dni (assume Px))))))

macro-∀sub : ∀{v α Ω Γ}
             → (w : Variable)
             → Ω , Γ ⊢ Λ v α
             → {_ : w isNotFreeIn [ Λ v α ]}
             → Ω , _ ⊢ Λ w (α [ varterm v / varterm w ])
macro-∀sub {v} {α} w T {pf} = arrowelim
                               (arrowintro (Λ v α)
                                (univintro w {pf} (univelim (varterm w)
                                 (assume (Λ v α)))))
                               T

--macro-∃sub : ∀{v α Ω Γ}
--             → (w : Variable)
--             → Ω , Γ ⊢ V v α
--             → Ω , _ ⊢ V w (α [ varterm v / varterm w ])
--macro-∃sub {v} {α} w T = existelim T
--                          (existintro (varterm v) {! w  !} ?)


-- Equivalences
he⊃ip : [ HE ] ⊃ ip Px A
he⊃ip = arrowintro (A ⇒ ∃x Px) (existelim (axiom 0 (Px ∷ []))
         (existintro y xvar (arrowintro A
          (arrowelim (assume (∃x Px ⇒ Py))
           (arrowelim (assume (A ⇒ ∃x Px)) (assume A))))))

ip⊃he : [ IP ] ⊃ he Px
ip⊃he = existelim
         (arrowelim
          (axiom 0 (Px ∷ ∃x Px ∷ []))
          (arrowintro (∃x Px) (assume (∃x Px))))
         (existintro x yvar (assume (∃x Px ⇒ Px)))

lem⊃glpo : [ LEM ] ⊃ glpo Px
lem⊃glpo = disjelim (axiom 0 (∃x Px ∷ []))
            (disjintro₂ (∀x ¬Px) (assume (∃x Px)) )
            (disjintro₁ (∃x Px) (univintro xvar
             (arrowintro Px (arrowelim (assume (¬∃x Px))
                             (existintro x xvar (assume Px))))))

glpo⊃lem : [ GLPO ] ⊃ lem A
glpo⊃lem = disjelim (axiom 0 (A ∷ []))
            (disjintro₂ A (univelim x (assume (∀x ¬A))))
            (disjintro₁ ¬A (existelim (assume (∃x A)) (assume A)))

dpn⊃hen : [ DPN ] ⊃ hen Px
dpn⊃hen = existelim (axiom 0 (¬Px ∷ [])) (existintro y yvar
           (arrowintro (∃x ¬Px) (arrowintro Py
            (existelim (assume (∃x ¬Px)) (arrowelim
             (univelim x (arrowelim
              (assume (¬¬Py ⇒ ∀x ¬¬Px)) (macro-dni (assume Py))))
             (assume ¬Px)))) ))

hen⊃dpn : [ HEN ] ⊃ dpn Px
hen⊃dpn = existelim (axiom 0 (¬Px ∷ []))
          (existintro y yvar (arrowintro ¬Py (univintro xvar
           (arrowintro Px (arrowelim
            (arrowelim (assume (∃x ¬¬Px ⇒ ¬¬Py))
             (existintro x xvar (macro-dni (assume Px))))
            (assume ¬Py))
           ))))

dnsu⊃wgmp : [ DNSU ] ⊃ wgmp Px
dnsu⊃wgmp = arrowintro (¬∀x Px) (arrowintro (¬∃x ¬Px)
             (arrowelim
              (arrowelim
               (axiom 0 (Px ∷ []))
               (univintro xvar (arrowintro ¬Px
                (arrowelim
                 (assume (¬∃x ¬Px))
                 (existintro x xvar (assume ¬Px))))))
              (assume (¬∀x Px))))

wgmp⊃dnsu : [ WGMP ] ⊃ dnsu Px
wgmp⊃dnsu = arrowintro (∀x ¬¬Px) (arrowintro (¬∀x Px)
             (arrowelim
              (arrowelim (axiom 0 (Px ∷ [])) (assume (¬∀x Px)))
              (arrowintro (∃x ¬Px) (existelim
               (assume (∃x ¬Px))
               (arrowelim (univelim x (assume (∀x ¬¬Px))) (assume ¬Px))))))

-- Proofs
lem⊃wlem : [ LEM ] ⊃ wlem A
lem⊃wlem = axiom 0 (¬A ∷ [])

dp⊃dpn : [ DP ] ⊃ dpn Px
dp⊃dpn = axiom 0 (¬Px ∷ [])

he⊃hen : [ HE ] ⊃ hen Px
he⊃hen = axiom 0 (¬Px ∷ [])

gmp⊃wgmp : [ GMP ] ⊃ wgmp Px
gmp⊃wgmp = arrowintro (¬∀x Px) (macro-dni (arrowelim
            (axiom 0 (Px ∷ []))
            (assume (¬∀x Px))))

dgp⊃wlem : [ DGP ] ⊃ wlem A
dgp⊃wlem = disjelim (axiom 0 (A ∷ ¬A ∷ []))
            (disjintro₁ ¬¬A (arrowintro A (arrowelim
             (arrowelim (assume (A ⇒ ¬A)) (assume A))
             (assume A))))
            (disjintro₂ ¬A (arrowintro ¬A (arrowelim (assume ¬A)
             (arrowelim (assume (¬A ⇒ A)) (assume ¬A)))))

glpoa⊃lem : [ GLPOA ] ⊃ lem A
glpoa⊃lem = disjelim (axiom 0 (A ∷ []))
             (disjintro₁ ¬A (univelim x (assume (∀x A))))
             (disjintro₂ A (existelim (assume (∃x ¬A)) (assume ¬A)))

glpoa⊃gmp : [ GLPOA ] ⊃ gmp Px
glpoa⊃gmp = arrowintro (¬∀x Px) (disjelim (axiom 0 (Px ∷ []))
             (existintro x xvar (arrowintro Px
              (arrowelim (assume (¬∀x Px)) (assume (∀x Px)))))
             (assume (∃x ¬Px)))

dp⊃ud : [ DP ] ⊃ ud Px A
dp⊃ud = arrowintro (∀x (Px ∨ A)) (existelim (axiom 0 (Px ∷ []))
         (disjelim (univelim y (assume (∀x (Px ∨ A))))
          (disjintro₁ A (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))
          (disjintro₂ (∀x Px) (assume A))))

dp⊃gmp : [ DP ] ⊃ gmp Px
dp⊃gmp = arrowintro (¬∀x Px) (existelim (axiom 0 (Px ∷ []))
          (existintro y xvar (arrowintro Py (arrowelim (assume (¬∀x Px))
           (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py))))))

-- Redundant by transitivity
-- dp⊃dnsu : [ DP ] ⊃ dnsu Px
-- dp⊃dnsu = arrowintro (∀x ¬¬Px) (arrowintro (¬∀x Px)
--            (existelim (axiom 0 (Px ∷ []))
--             (arrowelim
--              (univelim y (assume (∀x ¬¬Px)))
--              (arrowintro Py (arrowelim
--               (assume (¬∀x Px))
--               (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))))))

glpo⊃dpn : [ GLPO ] ⊃ dpn Px
glpo⊃dpn = disjelim (axiom 0 (Px ∷ []))
            (existintro y yvar (arrowintro ¬Py (assume (∀x ¬Px))))
            (existelim (assume (∃x Px))
             (existintro x yvar (arrowintro ¬Px
              (macro-∀sub xvar (univintro zvar
               (arrowintro Pz (arrowelim (assume ¬Px) (assume Px))))))))

he⊃dnse : [ HE ] ⊃ dnse Px
he⊃dnse = arrowintro (¬¬ (∃x Px)) (existelim (axiom 0 (Px ∷ []))
           (existintro y xvar (arrowintro ¬Py
            (arrowelim (assume (¬¬ (∃x Px))) (arrowintro (∃x Px)
             (arrowelim (assume ¬Py)
              (arrowelim (assume (∃x Px ⇒ Py)) (assume (∃x Px)))))))))

glpo⊃dnse : [ GLPO ] ⊃ dnse Px
glpo⊃dnse = arrowintro (¬¬ (∃x Px)) (disjelim (axiom 0 (Px ∷ []))
             (existintro x xvar (arrowintro ¬Px
              (arrowelim (assume (¬¬ (∃x Px)))
               (arrowintro (∃x Px) (existelim (assume (∃x Px))
                (arrowelim (univelim x (assume (∀x ¬Px))) (assume Px)))))))
             (existelim (assume (∃x Px)) (existintro x xvar
              (macro-dni (assume Px)))))

gmp⊃dnse : [ GMP ] ⊃ dnse Px
gmp⊃dnse = arrowintro (¬¬ (∃x Px)) (arrowelim (axiom 0 (¬Px ∷ []))
            (arrowintro (∀x ¬Px) (arrowelim (assume (¬¬ (∃x Px)))
             (arrowintro (∃x Px) (existelim (assume (∃x Px))
              (arrowelim (univelim x (assume (∀x ¬Px))) (assume Px)))))))

dpn⊃dnse : [ DPN ] ⊃ dnse Px
dpn⊃dnse = arrowintro (¬¬ (∃x Px)) (existelim (axiom 0 (Px ∷ []))
            (existintro y xvar (arrowintro ¬Py (arrowelim
             (assume (¬¬ (∃x Px)))
             (arrowintro (∃x Px) (existelim (assume (∃x Px))
              (arrowelim
               (univelim x (arrowelim (assume (¬Py ⇒ ∀x ¬Px)) (assume ¬Py)))
               (assume Px))))))))

glpoa⊃wgmp : [ GLPOA ] ⊃ wgmp Px
glpoa⊃wgmp = disjelim (axiom 0 (Px ∷ []))
              (arrowintro (¬∀x Px) (arrowintro (¬∃x ¬Px)
               (arrowelim (assume (¬∀x Px)) (assume (∀x Px)))))
              (arrowintro (¬∀x Px) (macro-dni (assume (∃x ¬Px))))


dp,efq,tt⊃dgp : DP ∷ EFQ ∷ [TT] ⊃ dgp A B
dp,efq,tt⊃dgp = let Φ = (Dy ⇒ A) ∧ (¬Dy ⇒ B) ⇒ ∀x ((Dx ⇒ A) ∧ (¬Dx ⇒ B))
                in  existelim (axiom 0 ((Dx ⇒ A) ∧ (¬Dx ⇒ B) ∷ []))
                     (disjelim (univelim y (axiom 4 []))
                      (disjintro₁ (B ⇒ A) (arrowintro A
                       (conjelim
                        (univelim t¹
                         (arrowelim (assume Φ)
                          (conjintro
                           (arrowintro Dy (assume A))
                           (arrowintro ¬Dy
                            (macro-efq-helper B
                             (arrowelim (assume ¬Dy) (assume Dy)))))))
                        (arrowelim (assume (¬Dt¹ ⇒ B)) (axiom 3 [])))))
                      (disjintro₂ (A ⇒ B) (arrowintro B
                       (conjelim
                        (univelim t⁰
                         (arrowelim (assume Φ)
                          (conjintro
                           (arrowintro Dy
                            (macro-efq-helper A
                             (arrowelim (assume ¬Dy) (assume Dy))))
                           (arrowintro ¬Dy (assume B)))))
                        (arrowelim (assume (Dt⁰ ⇒ A)) (axiom 2 []))))))

dp,tt⊃wlem : DP ∷ [TT] ⊃ wlem A
dp,tt⊃wlem = let Φ = (Dy ⇒ A) ∧ (¬Dy ⇒ ¬A) ⇒ ∀x ((Dx ⇒ A) ∧ (¬Dx ⇒ ¬A))
             in  existelim (axiom 0 ((Dx ⇒ A) ∧ (¬Dx ⇒ ¬A) ∷ []))
                  (disjelim (univelim y (axiom 3 []))
                   (disjintro₁ ¬¬A (arrowintro A
                    (conjelim
                     (univelim t¹
                      (arrowelim (assume Φ)
                       (conjintro
                        (arrowintro Dy (assume A))
                         (arrowintro ¬Dy (arrowintro A
                          (arrowelim (assume ¬Dy) (assume Dy)))))))
                     (arrowelim
                      (arrowelim (assume (¬Dt¹ ⇒ ¬A)) (axiom 2 []))
                      (assume A)))))
                   {!   !})
