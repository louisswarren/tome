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

GLPO GLPOA GMP WGMP DP HE DPN HEN DNSU DNSE UD IP : Variable → Scheme
LEM WLEM DGP : Scheme



lem wlem : Formula → Formula
lem  Φ = Φ ∨ ¬ Φ
wlem Φ = ¬ Φ ∨ ¬¬ Φ

LEM  = unaryscheme "LEM" lem
WLEM = unaryscheme "WLEM" wlem



dgp : Formula → Formula → Formula
dgp Φ Ψ  = (Φ ⇒ Ψ) ∨ (Ψ ⇒ Φ)

DGP = binaryscheme "DGP" dgp



glpo glpoa gmp wgmp : Variable → Formula → Formula
glpo  v f = ∀x ¬Φx ∨ ∃x Φx                   where Φx = f [! v / x ]; ¬Φx = ¬ Φx
glpoa v f = ∀x Φx ∨ ∃x ¬Φx                   where Φx = f [! v / x ]; ¬Φx = ¬ Φx
gmp   v f = ¬∀x Φx ⇒ ∃x ¬Φx                  where Φx = f [! v / x ]; ¬Φx = ¬ Φx
wgmp  v f = ¬∀x Φx ⇒ ¬¬(∃x ¬Φx)              where Φx = f [! v / x ]; ¬Φx = ¬ Φx

GLPO  v = unaryscheme "GLPO"  (glpo v)
GLPOA v = unaryscheme "GLPOA" (glpoa v)
GMP   v = unaryscheme "GMP"   (gmp v)
WGMP  v = unaryscheme "WGMP"  (wgmp v)



dp he dpn hen : Variable → Formula → Formula
dp  v f = ∃y(Φy ⇒ ∀x Φx)              where Φx = f [! v / x ]; Φy = f [! v / y ]
he  v f = ∃y(∃x Φx ⇒ Φy)              where Φx = f [! v / x ]; Φy = f [! v / y ]
dpn v f = dp v (¬ f)
hen v f = he v (¬ f)

DP  v = unaryscheme "DP"  (dp v)
HE  v = unaryscheme "HE"  (he v)
DPN v = unaryscheme "DPN" (dpn v)
HEN v = unaryscheme "HEN" (hen v)



dnsu dnse : Variable → Formula → Formula
dnsu v f = ∀x(¬¬ Φx) ⇒ ¬¬(∀x Φx)                         where Φx = f [! v / x ]
dnse v f = ¬¬(∃x Φx) ⇒ ∃x (¬¬ Φx)                        where Φx = f [! v / x ]

DNSU v = unaryscheme "DNSU" (dnsu v)
DNSE v = unaryscheme "DNSE" (dnse v)



ud ip : Variable → Formula → Formula → Formula
ud v f Ψ = ∀x (Φx ∨ Ψ) ⇒ (∀x Φx ∨ Ψ)                     where Φx = f [! v / x ]
ip v f Ψ = (Ψ ⇒ ∃x Φx) ⇒ ∃x(Ψ ⇒ Φx)                      where Φx = f [! v / x ]

UD v = binaryscheme "UD" (ud v)
IP v = binaryscheme "IP" (ip v)




Q = atom (mkprop "Q") []
P : Term → Formula
P t = atom (mkrel 1 "P") (t ∷ [])

Px = P x
Py = P y

¬Q = ¬ Q
¬Px = ¬ Px
¬Py = ¬ Py

¬¬Q = ¬¬ Q
¬¬Px = ¬¬ Px
¬¬Py = ¬¬ Py

-- Lemmae and macros

-- A macro cannot (with the current system) be proved discharge assumptions in
-- general, but when applied, Agda can prove its effect for a given case
macro-dni : ∀{α Ω Γ} → Ω , Γ ⊢ α → Ω , _ ⊢ (¬¬ α)
macro-dni {α} T = arrowintro (¬ α) (arrowelim (assume (¬ α)) T)

macro-contra : ∀{α β Ω Γ} → Ω , Γ ⊢ α ⇒ β → Ω , _ ⊢ (¬ β) ⇒ (¬ α)
macro-contra {α} {β} T = arrowintro (¬ β) (arrowintro α
                          (arrowelim (assume (¬ β)) (arrowelim T (assume α))))

macro-tne : ∀{α Ω Γ} → Ω , Γ ⊢ ¬¬(¬ α) → Ω , _ ⊢ ¬ α
macro-tne {α} T = arrowintro α (arrowelim T (macro-dni (assume α)))

-- Didn't need to prove this
--lemma01 : ⊢ (¬∃x ¬¬Px ⇒ (∃x ¬Px))
--lemma01 = arrowintro (¬∃x ¬¬Px) (existintro x xvar
--           (arrowintro Px (arrowelim (assume (¬∃x ¬¬Px))
--            (existintro x xvar (macro-dni (assume Px))))))

-- Equivalences
lem⊃glpo : [ LEM ] ⊃ glpo xvar Px
lem⊃glpo = disjelim (axiom 0 (∃x Px ∷ []))
            (disjintro₂ (∀x ¬Px) (assume (∃x Px)) )
            (disjintro₁ (∃x Px) (univintro xvar
             (arrowintro Px (arrowelim (assume (¬∃x Px))
                             (existintro x xvar (assume Px))))))

glpo⊃lem : [ GLPO xvar ] ⊃ lem Q
glpo⊃lem = disjelim (axiom 0 (Q ∷ []))
            (disjintro₂ Q (univelim x (assume (∀x ¬Q))))
            (disjintro₁ ¬Q (existelim (assume (∃x Q)) (assume Q)))

dpn⊃hen : [ DPN xvar ] ⊃ hen xvar Px
dpn⊃hen = existelim (axiom 0 (¬Px ∷ [])) (existintro y yvar
           (arrowintro (∃x ¬Px) (macro-tne (arrowelim
            (macro-contra (assume (¬¬Py ⇒ ∀x ¬¬Px)))
            (arrowintro (∀x ¬¬Px) (existelim
             (assume (∃x ¬Px))
             (arrowelim (univelim x (assume (∀x ¬¬Px))) (assume ¬Px))))))))

hen⊃dpn : [ HEN xvar ] ⊃ dpn xvar Px
hen⊃dpn = existelim (axiom 0 (¬Px ∷ []))
          (existintro y yvar (arrowintro ¬Py (univintro xvar (arrowintro Px
           (arrowelim
            (arrowelim
             (macro-contra (assume (∃x ¬¬Px ⇒ ¬¬Py)))
             (macro-dni (assume ¬Py)))
            (existintro x xvar (macro-dni (assume Px))))))))
