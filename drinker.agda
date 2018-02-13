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

LEM WLEM DGP GLPO GLPOA GMP WGMP DP HE DPN HEN DNSU DNSE UD IP : Scheme



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

macro-tollens : ∀{α β Ω Γ₁ Γ₂} → Ω , Γ₁ ⊢ α ⇒ β → Ω , Γ₂ ⊢ ¬ β → Ω , _ ⊢ ¬ α
macro-tollens {α} {β} T₁ T₂ = arrowintro α (arrowelim T₂
                              (arrowelim T₁ (assume α)))

macro-incons : ∀{α β Ω Γ₁ Γ₂ Γ₃}
               → Ω , Γ₁ ⊢ α ⇒ β
               → Ω , Γ₂ ⊢ ¬ β
               → Ω , Γ₃  ⊢ α
               → Ω , Γ₂ ++ Γ₁ ++ Γ₃ ⊢ ⊥
macro-incons {α} {β} T₁ T₂ T₃ = arrowelim T₂ (arrowelim T₁ T₃)


macro-tne : ∀{α Ω Γ} → Ω , Γ ⊢ ¬¬(¬ α) → Ω , _ ⊢ ¬ α
macro-tne {α} T = arrowintro α (arrowelim T (macro-dni (assume α)))

-- Didn't need to prove this
--lemma01 : ⊢ (¬∃x ¬¬Px ⇒ (∃x ¬Px))
--lemma01 = arrowintro (¬∃x ¬¬Px) (existintro x xvar
--           (arrowintro Px (arrowelim (assume (¬∃x ¬¬Px))
--            (existintro x xvar (macro-dni (assume Px))))))

-- Equivalences
lem⊃glpo : [ LEM ] ⊃ glpo Px
lem⊃glpo = disjelim (axiom 0 (∃x Px ∷ []))
            (disjintro₂ (∀x ¬Px) (assume (∃x Px)) )
            (disjintro₁ (∃x Px) (univintro xvar
             (arrowintro Px (arrowelim (assume (¬∃x Px))
                             (existintro x xvar (assume Px))))))

glpo⊃lem : [ GLPO ] ⊃ lem Q
glpo⊃lem = disjelim (axiom 0 (Q ∷ []))
            (disjintro₂ Q (univelim x (assume (∀x ¬Q))))
            (disjintro₁ ¬Q (existelim (assume (∃x Q)) (assume Q)))

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

s = texify dpn⊃hen
