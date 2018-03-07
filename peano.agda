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

PEANO = pax1 ∷ pax2 ∷ pax3 ∷ pax4 ∷ pax5 ∷ pax6 ∷ pax7 ∷ pax8 ∷ pax9 ∷ []

zero∨suc : PEANO , [] ⊢ (∀x (x ≈ pzero ∨ ∃y (x ≈ psuc y)))
zero∨suc = arrowelim
            (arrowelim (axiom 8 (x ≈ pzero ∨ ∃y (x ≈ psuc y) ∷ []))
             (disjintro₁ (∃y (pzero ≈ psuc y)) (univelim pzero (axiom 1 []))))
            (univintro xvar (arrowintro (x ≈ pzero ∨ ∃y (x ≈ psuc y))
             (disjelim (assume (x ≈ pzero ∨ ∃y (x ≈ psuc y)))
              (disjintro₂ (psuc x ≈ pzero) (existintro pzero yvar
               (arrowelim (univelim pzero
                (univelim x (axiom 6 []))) (assume (x ≈ pzero)))))
              (disjintro₂ (psuc x ≈ pzero) (existelim (assume (∃y (x ≈ psuc y)))
               (existintro (psuc y) yvar (arrowelim
                (univelim (psuc y) (univelim x (axiom 6 [])))
                (assume (x ≈ psuc y)))))))))


lift : ∀{Ω Γ α} → (ω : Scheme) → Ω , Γ ⊢ α → (ω ∷ Ω) , Γ ⊢ α
lift ω (axiom k xs) = axiom (suc k) xs
lift ω (assume α) = assume α
lift ω (arrowintro α T) = arrowintro α (lift ω T)
lift ω (arrowelim T₁ T₂) = arrowelim (lift ω T₁) (lift ω T₂)
lift ω (conjintro T₁ T₂) = conjintro (lift ω T₁) (lift ω T₂)
lift ω (conjelim T₁ T₂) = conjelim (lift ω T₁) (lift ω T₂)
lift ω (disjintro₁ β T) = disjintro₁ β (lift ω T)
lift ω (disjintro₂ α T) = disjintro₂ α (lift ω T)
lift ω (disjelim T₁ T₂ T₃) = disjelim (lift ω T₁) (lift ω T₂) (lift ω T₃)
lift ω (univintro v {pf}  T) = univintro v {pf} (lift ω T)
lift ω (univelim r T) = univelim r (lift ω T)
lift ω (existintro r v T) = existintro r v (lift ω T)
lift ω (existelim {_} {_} {_} {_} {_} {_} {pf} T₁ T₂)
      = existelim {_} {_} {_} {_} {_} {_} {pf} (lift ω T₁) (lift ω T₂)
