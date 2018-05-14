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

DNE EFQ LEM WLEM DGP GLPO GLPOA GMP WGMP DP HE DP' HE' DPN HEN DNSU DNSE UD IP : Scheme
FIN∀ FIN∃ : Scheme

dne : Formula → Formula
dne Φ = ¬¬ Φ ⇒ Φ

DNE = unaryscheme "DNE" dne

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



dp he dp' he' dpn hen : Formula → Formula
dp  Φx = ∃y(Φy ⇒ ∀x Φx)                                  where Φy = Φx [ x / y ]
he  Φx = ∃y(∃x Φx ⇒ Φy)                                  where Φy = Φx [ x / y ]
dp' Φx = ∃y(∀x(Φy ⇒ Φx))                                 where Φy = Φx [ x / y ]
he' Φx = ∃y(∀x(Φx ⇒ Φy))                                 where Φy = Φx [ x / y ]
dpn Φx = dp (¬ Φx)
hen Φx = he (¬ Φx)

DP  = unaryscheme "DP"  dp
HE  = unaryscheme "HE"  he
DP' = unaryscheme "DP'" dp'
HE' = unaryscheme "HE'" he'
DPN = unaryscheme "DPN" dpn
HEN = unaryscheme "HEN" hen



dnsu dnse : Formula → Formula
dnsu Φx = ∀x(¬¬ Φx) ⇒ ¬¬(∀x Φx)
dnse Φx = ¬¬(∃x Φx) ⇒ ∃x (¬¬ Φx)

DNSU = unaryscheme "DNSU" dnsu
DNSE = unaryscheme "DNSE" dnse


-- These are usually stated with Ψ instead of ∃x Ψ, but this is a simple way of
-- adding bounded variable requirements as x is certainly not free in ∃x Ψ.
-- If x is in fact not free in Ψ, then the existential can be eliminated
-- separately.
ud ip : Formula → Formula → Formula
ud Φx Ψ = ∀x (Φx ∨ (∃x Ψ)) ⇒ (∀x Φx ∨ ∃x Ψ)
ip Φx Ψ = (∃x Ψ ⇒ ∃x Φx) ⇒ ∃x(∃x Ψ ⇒ Φx)

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
¬Dt⁰ = ¬ Dt⁰
¬Dt¹ = ¬ Dt¹
Dx  = D x
¬Dx = ¬ Dx
Dy  = D y
¬Dy = ¬ Dy
[TT] : List Scheme
[TT] = nullaryscheme "DZ" (Dt⁰)
     ∷ nullaryscheme "DO" (¬Dt¹)
     ∷ nullaryscheme "DX" (∀x (D x ∨ ¬ (D x)))
     ∷ []


-- Use this to apply predicative schemes to propositional problems
fin∀ fin∃ : Formula → Formula → Formula
fin∀ Φ Ψ = ∀x ((Dx ⇒ Φ) ∧ (¬Dx ⇒ Ψ)) ⇒ (Φ ∧ Ψ)
FIN∀ = binaryscheme "FIN$\\forall$" fin∀

fin∃ Φ Ψ = ∃x ((Dx ⇒ Φ) ∧ (¬Dx ⇒ Ψ)) ⇒ (Φ ∨ Ψ)
FIN∃ = binaryscheme "FIN$\\exists$" fin∃


tt-fin∀ : ([TT] ⊃ FIN∀) (A ∷ B ∷ [])
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

tt-fin∃ : ([TT] ⊃ FIN∃) (A ∷ B ∷ [])
tt-fin∃ = arrowintro (∃x ((Dx ⇒ A) ∧ (¬Dx ⇒ B)))
           (existelim (assume (∃x ((Dx ⇒ A) ∧ (¬Dx ⇒ B))))
            (conjelim (assume ((Dx ⇒ A) ∧ (¬Dx ⇒ B)))
             (disjelim
              (univelim x (axiom 2 []))
              (disjintro₁ B (arrowelim (assume (Dx ⇒ A)) (assume Dx)))
              (disjintro₂ A (arrowelim (assume (¬Dx ⇒ B)) (assume ¬Dx))))))

[FIN] : List Scheme
[FIN] = FIN∀ ∷ FIN∃ ∷ []

-- Tex the rules
ax-d0 : [TT] , [] ⊢ _
ax-d0 = axiom 0 []

ax-d1 : [TT] , [] ⊢ _
ax-d1 = axiom 1 []

ax-d : [TT] , [] ⊢ _
ax-d = axiom 2 []

rule-d0 = texifyded ax-d0
rule-d1 = texifyded ax-d1
rule-d  = texifyded ax-d

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
-- We will use these together instead of (but equivalently to) DNE
[DNE,LEM,EFQ] : List Scheme
[DNE,LEM,EFQ] = DNE ∷ LEM ∷ EFQ ∷ []

dne⊃lem : ([ DNE ] ⊃ LEM) (A ∷ [])
dne⊃lem = arrowelim (axiom 0 (lem A ∷ [])) (arrowintro (¬ (lem A))
           (arrowelim (assume (¬ (lem A)))
            (disjintro₂ A (arrowintro A
             (arrowelim (assume (¬ (lem A))) (disjintro₁ ¬A (assume A)))))))

prop-dne-lem = texifyreduce [ DNE ] LEM (A ∷ []) dne⊃lem


dne⊃efq : ([ DNE ] ⊃ EFQ) (A ∷ [])
dne⊃efq = arrowintro ⊥ (arrowelim (axiom 0 (A ∷ [])) (arrowintro ¬A (assume ⊥)))

prop-dne-efq = texifyreduce [ DNE ] EFQ (A ∷ []) dne⊃efq


lem,efq⊃dne : (LEM ∷ EFQ ∷ [] ⊃ DNE) (A ∷ [])
lem,efq⊃dne = arrowintro ¬¬A (disjelim (axiom 0 (A ∷ []))
               (assume A)
               (arrowelim
                (axiom 1 (A ∷ []))
                (arrowelim (assume ¬¬A) (assume ¬A))))

prop-lem,efq-dne = texifyreduce (LEM ∷ EFQ ∷ []) DNE (A ∷ []) lem,efq⊃dne


he⊃ip : ([ HE ] ⊃ IP) (Px ∷ A ∷ [])
he⊃ip = arrowintro (∃x A ⇒ ∃x Px) (existelim (axiom 0 (Px ∷ []))
         (existintro y xvar (arrowintro (∃x A)
          (arrowelim (assume (∃x Px ⇒ Py))
           (arrowelim (assume (∃x A ⇒ ∃x Px)) (assume (∃x A)))))))

prop-he-ip = texifyreduce [ HE ] IP (Px ∷ A ∷ []) he⊃ip


ip⊃he : ([ IP ] ⊃ HE) (Px ∷ [])
ip⊃he = existelim
         (arrowelim
          (axiom 0 (Px ∷ Px ∷ []))
          (arrowintro (∃x Px) (assume (∃x Px))))
         (existintro x yvar (assume (∃x Px ⇒ Px)))

prop-ip-he = texifyreduce [ IP ] HE (Px ∷ []) ip⊃he


lem⊃glpo : ([ LEM ] ⊃ GLPO) (Px ∷ [])
lem⊃glpo = disjelim (axiom 0 (∃x Px ∷ []))
            (disjintro₂ (∀x ¬Px) (assume (∃x Px)) )
            (disjintro₁ (∃x Px) (univintro xvar
             (arrowintro Px (arrowelim (assume (¬∃x Px))
                             (existintro x xvar (assume Px))))))

prop-lem-glpo = texifyreduce [ LEM ] GLPO (Px ∷ []) lem⊃glpo


glpo⊃lem : ([ GLPO ] ⊃ LEM) (A ∷ [])
glpo⊃lem = disjelim (axiom 0 (A ∷ []))
            (disjintro₂ A (univelim x (assume (∀x ¬A))))
            (disjintro₁ ¬A (existelim (assume (∃x A)) (assume A)))

prop-glpo-lem = texifyreduce [ GLPO ] LEM (A ∷ []) glpo⊃lem


dpn⊃hen : ([ DPN ] ⊃ HEN) (Px ∷ [])
dpn⊃hen = existelim (axiom 0 (¬Px ∷ [])) (existintro y yvar
           (arrowintro (∃x ¬Px) (arrowintro Py
            (existelim (assume (∃x ¬Px)) (arrowelim
             (univelim x (arrowelim
              (assume (¬¬Py ⇒ ∀x ¬¬Px)) (macro-dni (assume Py))))
             (assume ¬Px)))) ))

--prop-dpn-hen = texifyreduce [ DPN ] HEN (Px ∷ [])


hen⊃dpn : ([ HEN ] ⊃ DPN) (Px ∷ [])
hen⊃dpn = existelim (axiom 0 (¬Px ∷ []))
          (existintro y yvar (arrowintro ¬Py (univintro xvar
           (arrowintro Px (arrowelim
            (arrowelim (assume (∃x ¬¬Px ⇒ ¬¬Py))
             (existintro x xvar (macro-dni (assume Px))))
            (assume ¬Py))
           ))))

--prop-hen-dpn = texifyreduce [ HEN ] DPN (Px ∷ [])


dnsu⊃wgmp : ([ DNSU ] ⊃ WGMP) (Px ∷ [])
dnsu⊃wgmp = arrowintro (¬∀x Px) (arrowintro (¬∃x ¬Px)
             (arrowelim
              (arrowelim
               (axiom 0 (Px ∷ []))
               (univintro xvar (arrowintro ¬Px
                (arrowelim
                 (assume (¬∃x ¬Px))
                 (existintro x xvar (assume ¬Px))))))
              (assume (¬∀x Px))))

prop-dnsu-wgmp = texifyreduce [ DNSU ] WGMP (Px ∷ []) dnsu⊃wgmp


wgmp⊃dnsu : ([ WGMP ] ⊃ DNSU) (Px ∷ [])
wgmp⊃dnsu = arrowintro (∀x ¬¬Px) (arrowintro (¬∀x Px)
             (arrowelim
              (arrowelim (axiom 0 (Px ∷ [])) (assume (¬∀x Px)))
              (arrowintro (∃x ¬Px) (existelim
               (assume (∃x ¬Px))
               (arrowelim (univelim x (assume (∀x ¬¬Px))) (assume ¬Px))))))

prop-wgmp-dnsu = texifyreduce [ WGMP ] DNSU (Px ∷ []) wgmp⊃dnsu



-- Reformulations

dp⊢dp' : [] , (dp Px) ∷ [] ⊢ dp' Px
dp⊢dp' = existelim (assume (dp Px))
          (existintro y yvar
          (univintro xvar (arrowintro Py (univelim x
           (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py))))))

dp'⊢dp : [] , (dp' Px) ∷ [] ⊢ dp Px
dp'⊢dp = existelim (assume (dp' Px))
          (existintro y yvar
          (arrowintro Py (univintro xvar
           (arrowelim (univelim x (assume (∀x (Py ⇒ Px)))) (assume Py)))))

prop-dp-alt = "\\begin{proposition} \\label{prop:dpalt}\n"
              >> "$\\DPi{P}$ is equivalent to $" >> texformula (dp' Px) >> "$\n"
              >> texifypfs dp⊢dp' dp'⊢dp
              >> "\\end{proposition}\n"

he⊢he' : [] , (he Px) ∷ [] ⊢ he' Px
he⊢he' = existelim (assume (he Px))
          (existintro y yvar
           (univintro xvar (arrowintro Px (arrowelim
            (assume (∃x Px ⇒ Py)) (existintro x xvar (assume Px))))))

he'⊢he : [] , (he' Px) ∷ [] ⊢ he Px
he'⊢he = existelim (assume (he' Px))
          (existintro y yvar
           (arrowintro (∃x Px) (existelim (assume (∃x Px))
            (arrowelim (univelim x (assume (∀x (Px ⇒ Py)))) (assume Px)))))

prop-he-alt = "\\begin{proposition} \\label{prop:healt}\n"
              >> "$\\HEi{P}$ is equivalent to $" >> texformula (he' Px) >> "$\n"
              >> texifypfs he⊢he' he'⊢he
              >> "\\end{proposition}\n"
-- Proofs

lemma:¬∀xPx⊢∃x¬Px : [DNE,LEM,EFQ] , ¬∀x Px ∷ [] ⊢ ∃x ¬Px
lemma:¬∀xPx⊢∃x¬Px = (arrowelim
                  (axiom 0 (∃x ¬Px ∷ []))
                  (arrowintro (¬∃x ¬Px)
                   (arrowelim
                    (assume (¬∀x Px))
                    (univintro xvar (arrowelim
                     (axiom 0 (Px ∷ []))
                     (arrowintro ¬Px (arrowelim
                      (assume (¬∃x ¬Px))
                      (existintro x xvar (assume ¬Px)))))))))

classical-gmp : ([DNE,LEM,EFQ] ⊃ GMP) (Px ∷ [])
classical-gmp = arrowintro (¬∀x Px) lemma:¬∀xPx⊢∃x¬Px

classical-dp : ([DNE,LEM,EFQ] ⊃ DP) (Px ∷ [])
classical-dp = disjelim (axiom 1 (∀x Px ∷ []))
                (existintro y yvar (arrowintro Py (assume (∀x Px))))
                (existelim
                 (lemma lemma:¬∀xPx⊢∃x¬Px)
                 (existintro x yvar
                 (arrowintro Px
                  (arrowelim
                   (axiom 2 (∀x Px ∷ []))
                   (arrowelim (assume ¬Px) (assume Px))))))

prop-classical-dp = texifyreducewith [DNE,LEM,EFQ] DP (Px ∷ [])
                     ("First\n" >> texifypt lemma:¬∀xPx⊢∃x¬Px
                      >> vspace >> "Now,\n")
                     classical-dp


lem⊃wlem : ([ LEM ] ⊃ WLEM) (A ∷ [])
lem⊃wlem = axiom 0 (¬A ∷ [])

prop-lem-wlem = texifyreduce [ LEM ] WLEM (A ∷ []) lem⊃wlem


dp⊃dpn : ([ DP ] ⊃ DPN) (Px ∷ [])
dp⊃dpn = axiom 0 (¬Px ∷ [])

--prop-dp-dpn = texifyreduce [ DP ] DPN (Px ∷ []) dp⊃dpn


he⊃hen : ([ HE ] ⊃ HEN) (Px ∷ [])
he⊃hen = axiom 0 (¬Px ∷ [])

--prop-he-hen = texifyreduce [ HE ] HEN (Px ∷ []) he⊃hen


gmp⊃wgmp : ([ GMP ] ⊃ WGMP) (Px ∷ [])
gmp⊃wgmp = arrowintro (¬∀x Px) (macro-dni (arrowelim
            (axiom 0 (Px ∷ []))
            (assume (¬∀x Px))))

prop-gmp-wgmp = texifyreduce [ GMP ] WGMP (Px ∷ []) gmp⊃wgmp


dgp⊃wlem : ([ DGP ] ⊃ WLEM) (A ∷ [])
dgp⊃wlem = disjelim (axiom 0 (A ∷ ¬A ∷ []))
            (disjintro₁ ¬¬A (arrowintro A (arrowelim
             (arrowelim (assume (A ⇒ ¬A)) (assume A))
             (assume A))))
            (disjintro₂ ¬A (arrowintro ¬A (arrowelim (assume ¬A)
             (arrowelim (assume (¬A ⇒ A)) (assume ¬A)))))

prop-dgp-wlem = texifyreduce [ DGP ] WLEM (A ∷ []) dgp⊃wlem


glpoa⊃lem : ([ GLPOA ] ⊃ LEM) (A ∷ [])
glpoa⊃lem = disjelim (axiom 0 (A ∷ []))
             (disjintro₁ ¬A (univelim x (assume (∀x A))))
             (disjintro₂ A (existelim (assume (∃x ¬A)) (assume ¬A)))

prop-glpoa-lem = texifyreduce [ GLPOA ] LEM (A ∷ []) glpoa⊃lem


glpoa⊃gmp : ([ GLPOA ] ⊃ GMP) (Px ∷ [])
glpoa⊃gmp = arrowintro (¬∀x Px) (disjelim (axiom 0 (Px ∷ []))
             (existintro x xvar (arrowintro Px
              (arrowelim (assume (¬∀x Px)) (assume (∀x Px)))))
             (assume (∃x ¬Px)))

prop-glpoa-gmp = texifyreduce [ GLPOA ] GMP (Px ∷ []) glpoa⊃gmp


dp⊃ud : ([ DP ] ⊃ UD) (Px ∷ A ∷ [])
dp⊃ud = arrowintro (∀x (Px ∨ ∃x A)) (existelim (axiom 0 (Px ∷ []))
         (disjelim (univelim y (assume (∀x (Px ∨ ∃x A))))
          (disjintro₁ (∃x A) (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))
          (disjintro₂ (∀x Px) (assume (∃x A)))))

prop-dp-ud = texifyreduce [ DP ] UD (Px ∷ A ∷ []) dp⊃ud


dp⊃gmp : ([ DP ] ⊃ GMP) (Px ∷ [])
dp⊃gmp = arrowintro (¬∀x Px) (existelim (axiom 0 (Px ∷ []))
          (existintro y xvar (arrowintro Py (arrowelim (assume (¬∀x Px))
           (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py))))))

prop-dp-gmp = texifyreduce [ DP ] GMP (Px ∷ []) dp⊃gmp


-- Redundant by transitivity
-- dp⊃dnsu : [ DP ] ⊃ dnsu Px
-- dp⊃dnsu = arrowintro (∀x ¬¬Px) (arrowintro (¬∀x Px)
--            (existelim (axiom 0 (Px ∷ []))
--             (arrowelim
--              (univelim y (assume (∀x ¬¬Px)))
--              (arrowintro Py (arrowelim
--               (assume (¬∀x Px))
--               (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))))))

glpo⊃dpn : ([ GLPO ] ⊃ DPN) (Px ∷ [])
glpo⊃dpn = disjelim (axiom 0 (Px ∷ []))
            (existintro y yvar (arrowintro ¬Py (assume (∀x ¬Px))))
            (existelim (assume (∃x Px))
             (existintro x yvar (arrowintro ¬Px
              (macro-∀sub xvar (univintro zvar
               (arrowintro Pz (arrowelim (assume ¬Px) (assume Px))))))))

--prop-glpo-dpn = texifyreduce [ GLPO ] DPN (Px ∷ []) glpo⊃dpn


he⊃dnse : ([ HE ] ⊃ DNSE) (Px ∷ [])
he⊃dnse = arrowintro (¬¬ (∃x Px)) (existelim (axiom 0 (Px ∷ []))
           (existintro y xvar (arrowintro ¬Py
            (arrowelim (assume (¬¬ (∃x Px))) (arrowintro (∃x Px)
             (arrowelim (assume ¬Py)
              (arrowelim (assume (∃x Px ⇒ Py)) (assume (∃x Px)))))))))

prop-he-dnse = texifyreduce [ HE ] DNSE (Px ∷ []) he⊃dnse


glpo⊃dnse : ([ GLPO ] ⊃ DNSE) (Px ∷ [])
glpo⊃dnse = arrowintro (¬¬ (∃x Px)) (disjelim (axiom 0 (Px ∷ []))
             (existintro x xvar (arrowintro ¬Px
              (arrowelim (assume (¬¬ (∃x Px)))
               (arrowintro (∃x Px) (existelim (assume (∃x Px))
                (arrowelim (univelim x (assume (∀x ¬Px))) (assume Px)))))))
             (existelim (assume (∃x Px)) (existintro x xvar
              (macro-dni (assume Px)))))

prop-glpo-dnse = texifyreduce [ GLPO ] DNSE (Px ∷ []) glpo⊃dnse


gmp⊃dnse : ([ GMP ] ⊃ DNSE) (Px ∷ [])
gmp⊃dnse = arrowintro (¬¬ (∃x Px)) (arrowelim (axiom 0 (¬Px ∷ []))
            (arrowintro (∀x ¬Px) (arrowelim (assume (¬¬ (∃x Px)))
             (arrowintro (∃x Px) (existelim (assume (∃x Px))
              (arrowelim (univelim x (assume (∀x ¬Px))) (assume Px)))))))

prop-gmp-dnse = texifyreduce [ GMP ] DNSE (Px ∷ []) gmp⊃dnse


dpn⊃dnse : ([ DPN ] ⊃ DNSE) (Px ∷ [])
dpn⊃dnse = arrowintro (¬¬ (∃x Px)) (existelim (axiom 0 (Px ∷ []))
            (existintro y xvar (arrowintro ¬Py (arrowelim
             (assume (¬¬ (∃x Px)))
             (arrowintro (∃x Px) (existelim (assume (∃x Px))
              (arrowelim
               (univelim x (arrowelim (assume (¬Py ⇒ ∀x ¬Px)) (assume ¬Py)))
               (assume Px))))))))

--prop-dpn-dnse = texifyreduce [ DPN ] DNSE (Px ∷ []) dpn⊃dnse


glpoa⊃wgmp : ([ GLPOA ] ⊃ WGMP) (Px ∷ [])
glpoa⊃wgmp = disjelim (axiom 0 (Px ∷ []))
              (arrowintro (¬∀x Px) (arrowintro (¬∃x ¬Px)
               (arrowelim (assume (¬∀x Px)) (assume (∀x Px)))))
              (arrowintro (¬∀x Px) (macro-dni (assume (∃x ¬Px))))

prop-glpoa-wgmp = texifyreduce [ GLPOA ] WGMP (Px ∷ []) glpoa⊃wgmp


lemma:dp,efq,tt⊃dgp1 : DP ∷ EFQ ∷ [TT] , _ ⊢ (A ⇒ B) ∨ (B ⇒ A)
lemma:dp,efq,tt⊃dgp1 = let Φ = (Dy ⇒ A) ∧ (¬Dy ⇒ B) ⇒ ∀x ((Dx ⇒ A) ∧ (¬Dx ⇒ B))
                       in (disjintro₁ (B ⇒ A) (arrowintro A
                           (conjelim
                            (univelim t¹
                             (arrowelim (assume Φ)
                              (conjintro
                               (arrowintro Dy (assume A))
                               (arrowintro ¬Dy
                                (macro-efq-helper B
                                 (arrowelim (assume ¬Dy) (assume Dy)))))))
                            (arrowelim (assume (¬Dt¹ ⇒ B)) (axiom 3 [])))))

lemma:dp,efq,tt⊃dgp2 : DP ∷ EFQ ∷ [TT] , _ ⊢ (A ⇒ B) ∨ (B ⇒ A)
lemma:dp,efq,tt⊃dgp2 = let Φ = (Dy ⇒ A) ∧ (¬Dy ⇒ B) ⇒ ∀x ((Dx ⇒ A) ∧ (¬Dx ⇒ B))
                       in (disjintro₂ (A ⇒ B) (arrowintro B
                           (conjelim
                            (univelim t⁰
                             (arrowelim (assume Φ)
                              (conjintro
                               (arrowintro Dy
                                (macro-efq-helper A
                                 (arrowelim (assume ¬Dy) (assume Dy))))
                               (arrowintro ¬Dy (assume B)))))
                            (arrowelim (assume (Dt⁰ ⇒ A)) (axiom 2 [])))))

dp,efq,tt⊃dgp : (DP ∷ EFQ ∷ [TT] ⊃ DGP) (A ∷ B ∷ [])
dp,efq,tt⊃dgp = let Φ = (Dy ⇒ A) ∧ (¬Dy ⇒ B) ⇒ ∀x ((Dx ⇒ A) ∧ (¬Dx ⇒ B))
                in  existelim (axiom 0 ((Dx ⇒ A) ∧ (¬Dx ⇒ B) ∷ []))
                     (disjelim (univelim y (axiom 4 []))
                      (lemma lemma:dp,efq,tt⊃dgp1)
                      (lemma lemma:dp,efq,tt⊃dgp2))

prop-dp,efq,tt-dgp = texifyreducewith (DP ∷ EFQ ∷ [TT]) DGP (A ∷ B ∷ [])
                      ("First\n" >> texifypt lemma:dp,efq,tt⊃dgp1 >>
                       vspace >> "and\n" >> texifypt lemma:dp,efq,tt⊃dgp2 >>
                       vspace >> "Now,\n")
                      dp,efq,tt⊃dgp


lemma:dp,tt⊃wlem1 : (DP ∷ [TT]) , _ ⊢ _
lemma:dp,tt⊃wlem1 = let Φ = (Dy ⇒ ¬¬A) ∧ (¬Dy ⇒ ¬A) ⇒ ∀x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                    in (disjintro₁ ¬¬A (arrowintro A
                        (conjelim
                         (univelim t¹
                          (arrowelim (assume Φ)
                           (conjintro
                            (arrowintro Dy (macro-dni (assume A)))
                            (arrowintro ¬Dy (arrowintro A
                             (arrowelim (assume ¬Dy) (assume Dy)))))))
                         (arrowelim
                          (arrowelim (assume (¬Dt¹ ⇒ ¬A)) (axiom 2 []))
                          (assume A)))))

lemma:dp,tt⊃wlem2 : (DP ∷ [TT]) , _ ⊢ _
lemma:dp,tt⊃wlem2 = let Φ = (Dy ⇒ ¬¬A) ∧ (¬Dy ⇒ ¬A) ⇒ ∀x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                    in (disjintro₂ ¬A (arrowintro ¬A
                        (conjelim
                         (univelim t⁰
                          (arrowelim (assume Φ)
                           (conjintro
                            (arrowintro Dy (arrowintro ¬A
                             (arrowelim (assume ¬Dy) (assume Dy))))
                            (arrowintro ¬Dy (assume ¬A)))))
                         (arrowelim
                          (arrowelim (assume (Dt⁰ ⇒ ¬¬A)) (axiom 1 []))
                          (assume ¬A)))))

dp,tt⊃wlem : (DP ∷ [TT] ⊃ WLEM) (A ∷ [])
dp,tt⊃wlem = let Φ = (Dy ⇒ ¬¬A) ∧ (¬Dy ⇒ ¬A) ⇒ ∀x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
             in  existelim (axiom 0 ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A) ∷ []))
                  (disjelim (univelim y (axiom 3 []))
                   (lemma lemma:dp,tt⊃wlem1)
                   (lemma lemma:dp,tt⊃wlem2))

prop-dp,tt-wlem = texifyreducewith (DP ∷ [TT]) WLEM (A ∷ [])
                   ("First\n" >> texifypt lemma:dp,tt⊃wlem1 >>
                    vspace >> "and\n" >> texifypt lemma:dp,tt⊃wlem2 >>
                    vspace >> "Now,\n")
                    dp,tt⊃wlem

lemma:he,efq,tt⊃dgp1 : HE ∷ EFQ ∷ [TT] , _ ⊢ _
lemma:he,efq,tt⊃dgp1 = let Φ = ∃x ((Dx ⇒ A) ∧ (¬Dx ⇒ B)) ⇒ ((Dy ⇒ A) ∧ (¬Dy ⇒ B))
                       in (disjintro₂ (A ⇒ B) (arrowintro B
                        (conjelim
                         (arrowelim (assume Φ)
                          (existintro t¹ xvar
                           (conjintro
                            (arrowintro Dt¹ (macro-efq-helper A
                             (arrowelim (axiom 3 []) (assume Dt¹))))
                            (arrowintro ¬Dt¹ (assume B)))))
                         (arrowelim (assume (Dy ⇒ A)) (assume Dy)))))

lemma:he,efq,tt⊃dgp2 : HE ∷ EFQ ∷ [TT] , _ ⊢ _
lemma:he,efq,tt⊃dgp2 = let Φ = ∃x ((Dx ⇒ A) ∧ (¬Dx ⇒ B)) ⇒ ((Dy ⇒ A) ∧ (¬Dy ⇒ B))
                       in (disjintro₁ (B ⇒ A) (arrowintro A
                        (conjelim
                         (arrowelim (assume Φ)
                          (existintro t⁰ xvar
                           (conjintro
                            (arrowintro Dt⁰ (assume A))
                            (arrowintro ¬Dt⁰ (macro-efq-helper B (arrowelim
                             (assume ¬Dt⁰) (axiom 2 [])))))))
                         (arrowelim (assume (¬Dy ⇒ B)) (assume ¬Dy)))))

he,efq,tt⊃dgp : (HE ∷ EFQ ∷ [TT] ⊃ DGP) (A ∷ B ∷ [])
he,efq,tt⊃dgp = let Φ = ∃x ((Dx ⇒ A) ∧ (¬Dx ⇒ B)) ⇒ ((Dy ⇒ A) ∧ (¬Dy ⇒ B))
                 in  existelim (axiom 0 ((Dx ⇒ A) ∧ (¬Dx ⇒ B) ∷ []))
                      (disjelim (univelim y (axiom 4 []))
                        (lemma lemma:he,efq,tt⊃dgp1)
                        (lemma lemma:he,efq,tt⊃dgp2)
                       )

prop-he,efq,tt-dgp = texifyreducewith (HE ∷ EFQ ∷ [TT]) DGP (A ∷ B ∷ [])
                   ("First\n" >> texifypt lemma:he,efq,tt⊃dgp1 >>
                    vspace >> "and\n" >> texifypt lemma:he,efq,tt⊃dgp2 >>
                    vspace >> "Now,\n")
                    he,efq,tt⊃dgp

lemma:he,tt⊃wlem1 : HE ∷ [TT] , _ ⊢ _
lemma:he,tt⊃wlem1 = let Φ = ∃x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A)) ⇒ ((Dy ⇒ ¬¬A) ∧ (¬Dy ⇒ ¬A))
                    in (disjintro₂ ¬A (arrowintro ¬A
                    (conjelim
                     (arrowelim (assume Φ)
                      (existintro t¹ xvar
                       (conjintro
                        (arrowintro Dt¹
                         (arrowintro ¬A (arrowelim (axiom 2 []) (assume Dt¹))))
                        (arrowintro ¬Dt¹ (assume ¬A)))))
                     (arrowelim
                      (arrowelim
                       (assume (Dy ⇒ ¬¬A))
                       (assume Dy))
                      (assume ¬A)))))

lemma:he,tt⊃wlem2 : HE ∷ [TT] , _ ⊢ _
lemma:he,tt⊃wlem2 = let Φ = ∃x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A)) ⇒ ((Dy ⇒ ¬¬A) ∧ (¬Dy ⇒ ¬A))
                    in (disjintro₁ ¬¬A (arrowintro A
                    (conjelim
                     (arrowelim (assume Φ)
                      (existintro t⁰ xvar
                       (conjintro
                        (arrowintro Dt⁰ (macro-dni (assume A)))
                        (arrowintro ¬Dt⁰
                         (arrowintro A
                          (arrowelim (assume ¬Dt⁰) (axiom 1 [])))))))
                     (arrowelim
                      (arrowelim (assume (¬Dy ⇒ ¬A)) (assume ¬Dy))
                      (assume A)))))

he,tt⊃wlem : (HE ∷ [TT] ⊃ WLEM) (A ∷ [])
he,tt⊃wlem = let Φ = ∃x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A)) ⇒ ((Dy ⇒ ¬¬A) ∧ (¬Dy ⇒ ¬A))
             in  existelim (axiom 0 ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A) ∷ []))
                  (disjelim (univelim y (axiom 3 []))
                        (lemma lemma:he,tt⊃wlem1)
                        (lemma lemma:he,tt⊃wlem2))

prop-he,tt-wlem = texifyreducewith (HE ∷ [TT]) WLEM (A ∷ []) (extractlemmas he,tt⊃wlem) he,tt⊃wlem


lemma:gmp,tt⊃wlem1 : GMP ∷ [TT] , _ ⊢ _
lemma:gmp,tt⊃wlem1 = let Φ = ∀x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                         Ψ = ¬((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                     in (arrowintro Φ (arrowelim
                    (conjelim
                     (univelim t⁰ (assume Φ))
                     (arrowelim (assume (Dt⁰ ⇒ ¬¬A)) (axiom 1 [])))
                    (conjelim
                     (univelim t¹ (assume Φ))
                     (arrowelim (assume (¬Dt¹ ⇒ ¬A)) (axiom 2 [])))))

lemma:gmp,tt⊃wlem2 : GMP ∷ [TT] , _ ⊢ _
lemma:gmp,tt⊃wlem2 = let Φ = ∀x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                         Ψ = ¬((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                     in (disjintro₁ ¬¬A (arrowintro A
                    (arrowelim (assume Ψ)
                     (conjintro
                      (arrowintro Dx (macro-dni (assume A)))
                      (arrowintro ¬Dx (arrowintro A
                       (arrowelim (assume ¬Dx) (assume Dx))))))))

lemma:gmp,tt⊃wlem3 : GMP ∷ [TT] , _ ⊢ _
lemma:gmp,tt⊃wlem3 = let Φ = ∀x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                         Ψ = ¬((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                     in (disjintro₂ ¬A (arrowintro ¬A
                    (arrowelim (assume Ψ)
                     (conjintro
                      (arrowintro Dx (arrowintro ¬A
                       (arrowelim (assume ¬Dx) (assume Dx))))
                      (arrowintro ¬Dx (assume ¬A))))))

gmp,tt⊃wlem : (GMP ∷ [TT] ⊃ WLEM) (A ∷ [])
gmp,tt⊃wlem = let Φ = ∀x ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                  Ψ = ¬((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
              in existelim
                  (arrowelim
                   (axiom 0 ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A) ∷ []))
                   (lemma lemma:gmp,tt⊃wlem1))
                  (disjelim (univelim x (axiom 3 []))
                   (lemma lemma:gmp,tt⊃wlem2)
                   (lemma lemma:gmp,tt⊃wlem3))

prop-gmp,tt-wlem = texifyreducewith (GMP ∷ [TT]) WLEM (A ∷ []) (extractlemmas gmp,tt⊃wlem) gmp,tt⊃wlem


dp,lem⊃glpoa : (DP ∷ LEM ∷ [] ⊃ GLPOA) (Px ∷ [])
dp,lem⊃glpoa = existelim (axiom 0 (Px ∷ [])) (disjelim (axiom 1 (Py ∷ []))
                (disjintro₁ (∃x ¬Px)
                 (arrowelim (assume (Py ⇒ ∀x Px)) (assume Py)))
                (disjintro₂ (∀x Px) (existintro y xvar (assume ¬Py))))

prop-dp,lem-glpoa = texifyreduce (DP ∷ LEM ∷ []) GLPOA (Px ∷ []) dp,lem⊃glpoa


lemma:dnse,tt⊃wlem1 : DNSE ∷ [TT] , _ ⊢ _
lemma:dnse,tt⊃wlem1 = let Φ = ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                      in (arrowintro ¬¬A (arrowelim
                          (arrowintro ((Dt⁰ ⇒ ¬¬A) ∧ (¬Dt⁰ ⇒ ¬A))
                           (arrowelim
                            (assume (¬∃x Φ))
                            (existintro t⁰ xvar
                             (assume ((Dt⁰ ⇒ ¬¬A) ∧ (¬Dt⁰ ⇒ ¬A))))))
                          (conjintro
                           (arrowintro Dt⁰ (assume ¬¬A))
                           (arrowintro ¬Dt⁰ (arrowintro A
                            (arrowelim (assume ¬Dt⁰) (axiom 1 [])))))))

lemma:dnse,tt⊃wlem2 : DNSE ∷ [TT] , _ ⊢ _
lemma:dnse,tt⊃wlem2 = let Φ = ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                      in (arrowintro ¬A (arrowelim
                           (arrowintro ((Dt¹ ⇒ ¬¬A) ∧ (¬Dt¹ ⇒ ¬A))
                            (arrowelim
                             (assume (¬∃x Φ))
                             (existintro t¹ xvar
                              (assume ((Dt¹ ⇒ ¬¬A) ∧ (¬Dt¹ ⇒ ¬A))))))
                           (conjintro
                            (arrowintro Dt¹ (arrowintro ¬A
                             (arrowelim (axiom 2 []) (assume Dt¹))))
                            (arrowintro ¬Dt¹ (assume ¬A)))))

lemma:dnse,tt⊃wlem3 : DNSE ∷ [TT] , _ ⊢ _
lemma:dnse,tt⊃wlem3 = let Φ = ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                      in (disjintro₂ ¬A (arrowintro ¬A
                          (arrowelim
                           (assume (¬¬ Φ))
                           (arrowintro Φ (conjelim (assume Φ)
                            (arrowelim (arrowelim (assume (Dx ⇒ ¬¬A)) (assume Dx)) (assume ¬A)))))))

lemma:dnse,tt⊃wlem4 : DNSE ∷ [TT] , _ ⊢ _
lemma:dnse,tt⊃wlem4 = let Φ = ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
                      in (disjintro₁ ¬¬A (arrowintro A
                          (arrowelim
                           (assume (¬¬ Φ))
                           (arrowintro Φ (conjelim (assume Φ)
                            (arrowelim (macro-dni (assume A)) (arrowelim (assume (¬Dx ⇒ ¬A)) (assume ¬Dx))))))))

dnse,tt⊃wlem : (DNSE ∷ [TT] ⊃ WLEM) (A ∷ [])
dnse,tt⊃wlem = let Φ = ((Dx ⇒ ¬¬A) ∧ (¬Dx ⇒ ¬A))
               in existelim (arrowelim (axiom 0 (Φ ∷ []))
                   (arrowintro (¬∃x Φ) (arrowelim (lemma lemma:dnse,tt⊃wlem1) (lemma lemma:dnse,tt⊃wlem2))))
                   (disjelim (univelim x (axiom 3 [])) (lemma lemma:dnse,tt⊃wlem3) (lemma lemma:dnse,tt⊃wlem4))

prop-dnse,tt-wlem = texifyreducewith (DNSE ∷ [TT]) WLEM (A ∷ []) (extractlemmas dnse,tt⊃wlem) dnse,tt⊃wlem

decidable : [ LEM ] , [] ⊢ ∀x (Px ∨ ¬Px)
decidable = univintro xvar (axiom 0 (Px ∷ []))

clearpage = "\\clearpage\n"

-- printouts
appendix : String
appendix = ""
           >> "\n" >> prop-dne-lem
           >> "\n" >> prop-dne-efq
           >> "\n" >> prop-lem,efq-dne
           >> "\n" >> prop-he-ip >> clearpage
           >> "\n" >> prop-ip-he
           >> "\n" >> prop-lem-glpo
           >> "\n" >> prop-glpo-lem
           >> "\n" >> prop-dnsu-wgmp >> clearpage
           >> "\n" >> prop-wgmp-dnsu
           >> "\n" >> prop-dp-alt >> clearpage
           >> "\n" >> prop-he-alt
           >> "\n" >> prop-classical-dp
           >> "\n" >> prop-lem-wlem >> clearpage
           >> "\n" >> prop-gmp-wgmp
           >> "\n" >> prop-dgp-wlem
           >> "\n" >> prop-glpoa-lem
           >> "\n" >> prop-glpoa-gmp
           >> "\n" >> prop-dp-ud >> clearpage
           >> "\n" >> prop-dp-gmp
           >> "\n" >> prop-he-dnse
           >> "\n" >> prop-glpo-dnse >> clearpage
           >> "\n" >> prop-gmp-dnse
           >> "\n" >> prop-glpoa-wgmp >> clearpage
           >> "\n" >> prop-dp,efq,tt-dgp >> clearpage
           >> "\n" >> prop-dp,tt-wlem >> clearpage
           >> "\n" >> prop-he,efq,tt-dgp >> clearpage
           >> "\n" >> prop-he,tt-wlem >> clearpage
           >> "\n" >> prop-gmp,tt-wlem >> clearpage
           >> "\n" >> prop-dp,lem-glpoa >> clearpage
           >> "\n" >> prop-dnse,tt-wlem
