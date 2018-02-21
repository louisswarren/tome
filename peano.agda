open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Formula
open import Deduction
open import Texify

open import common
open import sugar


-- Peano primatives
ppzero  = mkconst "0"
ppsuc   = mkfunc 1 "S"
ppeqs   = mkrel 2 "="
ppisnat = mkrel 1 "isnat"

-- Peano syntax sugar
pzero = functerm ppzero []

psuc : Term → Term
psuc t = functerm ppsuc (t ∷ [])

_≈_ : Term → Term → Formula
s ≈ t = atom ppeqs (s ∷ t ∷ [])
infixr 1000 _≈_

pisnat : Term → Formula
pisnat t = atom ppisnat (t ∷ [])

∀x∈ℕ ∀y∈ℕ : Formula → Formula
∀x∈ℕ Φ = ∀x (pisnat x ⇒ Φ)
∀y∈ℕ Φ = ∀y (pisnat y ⇒ Φ)

-- Peano axioms
-- All but induction are 0-ary schemes
pax1 = nullaryscheme "Pzero" (pisnat pzero)
pax2 = nullaryscheme "Prefl" (∀x (x ≈ x))
pax3 = nullaryscheme "Psymm" (∀x (∀y (x ≈ y ⇒ y ≈ x)))
pax4 = nullaryscheme "Ptran" (∀x (∀y (∀z (x ≈ y ⇒ y ≈ x ⇒ x ≈ z))))
pax5 = nullaryscheme "Pclos" (∀x (∀y (pisnat x ⇒ x ≈ y ⇒ pisnat y)))
pax6 = nullaryscheme "Psucn" (∀x (pisnat x ⇔ pisnat (psuc x)))
pax7 = nullaryscheme "Psucc" (∀x (∀y (x ≈ y ⇒ psuc x ≈ psuc y)))
pax8 = nullaryscheme "Pinfi" (∀x (¬ (psuc x ≈ pzero)))

-- For simplicity, include a parametrised induction by the free variable

induction : Variable → Vec Formula 1 → Formula
induction v (α ∷ []) = (α [ varterm v / pzero ])
                       ⇒ Λ v (α ⇒ (α [ varterm v / psuc (varterm v) ]))
                       ⇒ Λ v α
pax9fv : Variable → Scheme
pax9fv v = scheme 1 "Pindu" (induction v)

pax9 = pax9fv xvar

-- Axiom required in minimal logic for collapsing arithmetic absurdities
paxm = nullaryscheme "Pmini" (∀x (psuc x ≈ pzero ⇒ psuc pzero ≈ pzero))


zero∨suc : pax9 ∷ pax2 ∷ pax7 ∷ [] , [] ⊢ (∀x (x ≈ pzero ∨ ∃y (x ≈ psuc y)))
zero∨suc = arrowelim
            (arrowelim (axiom 0 (x ≈ pzero ∨ ∃y (x ≈ psuc y) ∷ []))
             (disjintro₁ (∃y (pzero ≈ psuc y)) (univelim pzero (axiom 1 []))))
            (univintro xvar (arrowintro (x ≈ pzero ∨ ∃y (x ≈ psuc y))
             (disjelim (assume (x ≈ pzero ∨ ∃y (x ≈ psuc y)))
              (disjintro₂ (psuc x ≈ pzero) (existintro pzero yvar
               (arrowelim (univelim pzero
                (univelim x (axiom 2 []))) (assume (x ≈ pzero)))))
              (disjintro₂ (psuc x ≈ pzero) (existelim (assume (∃y (x ≈ psuc y)))
               (existintro (psuc y) yvar (arrowelim
                (univelim (psuc y) (univelim x (axiom 2 [])))
                (assume (x ≈ psuc y)))))))))
