open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Sigma

open import Deduction
open import Ensemble
open import List
  hiding (Any ; any)
  renaming (
    All        to All[]        ;
    all        to all[]        ;
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    decide∈    to decide[∈]    )
open import Formula
open import Vec

open import Texify

open import sugar


LPO DNE EFQ LEM WLEM DGP GLPO GLPOA GMP WGMP DP HE DPN HEN DNSU DNSE UD IP CD : Scheme


lpo : Formula → Formula → Formula
lpo Φx Ψx = ∀x (Φx ∨ Ψx) ⇒ ∀x Φx ∨ ∃x Ψx

LPO = binaryscheme "LPO" lpo

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



dp he dpn hen : Formula → Formula
dp  Φx = ∃x(Φx ⇒ ∀x Φx)
he  Φx = ∃x(∃x Φx ⇒ Φx)
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

cd : Formula → Formula → Formula
cd Φx Ψ = ∀x (Φx ∨ ∃x Ψ) ⇒ ∀x Φx ∨ ∃x Ψ

CD = binaryscheme "CD" cd


-- These are usually stated with Ψ instead of ∃x Ψ, but this is a simple way of
-- adding bounded variable requirements as x is certainly not free in ∃x Ψ.
-- If x is in fact not free in Ψ, then the existential can be eliminated
-- separately.
ud ip : Formula → Formula → Formula
ud Φx Ψ = ∀x (Φx ∨ (∃x Ψ)) ⇒ (∀x Φx ∨ ∃x Ψ)
ip Φx Ψ = (∃x Ψ ⇒ ∃x Φx) ⇒ ∃x(∃x Ψ ⇒ Φx)

UD = binaryscheme "UD" ud
IP = binaryscheme "IP" ip







dne→lem : ⊢₁ dne → ⊢₁ lem
dne→lem ⊢dne α = close
                  (∅ ∪  ((α ∨ (α ⇒ atom (mkrel zero zero) []) ⇒ atom (mkrel zero zero) [])   ~   ((List.[ refl ] -∷ ∅) ∪ (α ~ (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅))))))
                  (arrowelim
                   (cite "DNE" (⊢dne (α ∨ ¬ α)))
                   (arrowintro (¬ (α ∨ ¬ α))
                    (arrowelim
                     (assume (¬ (α ∨ ¬ α)))
                     (disjintro₂ α
                      (arrowintro α
                       (arrowelim
                        (assume (¬ (α ∨ ¬ α)))
                        (disjintro₁ (¬ α)
                         (assume α))))))))
DNE⊃LEM : DNE ∷ [] ⊃ LEM
DNE⊃LEM (⊢DNE ∷ []) (α ∷ []) = dne→lem (descheme₁ ⊢DNE) α


dne→efq : ⊢₁ dne → ⊢₁ efq
dne→efq ⊢dne α = close (⊥ ~ (∅ ∪ (¬ α ~ ((¬ α ∷ [ refl ]) -∷ ∅)))) (arrowintro ⊥ (arrowelim (cite "DNE" (⊢dne α)) (arrowintro (¬ α) (assume ⊥))))
DNE⊃EFQ : DNE ∷ [] ⊃ EFQ
DNE⊃EFQ (⊢DNE ∷ []) (α ∷ []) = dne→efq (descheme₁ ⊢DNE) α

lem,efq→dne : ⊢₁ lem → ⊢₁ efq → ⊢₁ dne
lem,efq→dne ⊢lem ⊢efq α = close (¬¬ α ~  ((∅ ∪ (α ~ ([ refl ] -∷ ∅))) ∪   (¬ α ~ (∅ ∪ (((¬ α ∷ [ refl ]) -∷ ∅) ∪ ([ refl ] -∷ ∅)))))) (arrowintro (¬¬ α) (disjelim (cite "LEM" (⊢lem α)) (assume α) (arrowelim (cite "EFQ" (⊢efq α)) (arrowelim (assume (¬¬ α)) (assume (¬ α))))))
LEM,EFQ⊃DNE : LEM ∷ EFQ ∷ [] ⊃ DNE
LEM,EFQ⊃DNE (⊢LEM ∷ ⊢EFQ ∷ []) (α ∷ []) = lem,efq→dne (descheme₁ ⊢LEM) (descheme₁ ⊢EFQ) α


he→ip : ⊢₁ he → ⊢₂ ip
he→ip ⊢he α β = close ((∃x β ⇒ ∃x α) ~  (∅ ∪   ((∃x α ⇒ α) ~(∃x β ~ (((∃x β ∷ [ refl ]) -∷ ∅) ∪  (((∃x β ∷ ((∃x α ⇒ α) ∷ [ refl ])) -∷ ∅) ∪ ([ refl ] -∷ ∅))))))) (arrowintro (∃x β ⇒ ∃x α) (existelim (V∣ xvar (∃x β ⇒ α) ∷  ((∃x α ⇒ α) ~   (∃x β ~(((∃x β ∷ [ refl ]) -∷ ∅) ∪ (((V∣ xvar β ⇒ V∣ xvar α) ∷ ∅) ∪ (V∣ xvar β ∷ ∅)))))) (cite "HE" (⊢he α)) (existintro x xvar (ident (∃x β ⇒ α) xvar) (arrowintro (∃x β) (arrowelim (assume (∃x α ⇒ α)) (arrowelim (assume (∃x β ⇒ ∃x α)) (assume (∃x β))))))))
HE⊃IP : HE ∷ [] ⊃ IP
HE⊃IP (⊢HE ∷ []) (α ∷ β ∷ []) = he→ip (descheme₁ ⊢HE) α β


ip→he : ⊢₂ ip → ⊢₁ he
ip→he ⊢ip α = close ((∅ ∪ (∃x α ~ ([ refl ] -∷ ∅))) ∪ ((∃x α ⇒ α) ~ ([ refl ] -∷ ∅))) (existelim (V∣ xvar (∃x α ⇒ α) ∷ ((∃x α ⇒ α) ~ ([ refl ] -∷ ∅))) (arrowelim (cite "IP" (⊢ip α α)) (arrowintro (∃x α) (assume (∃x α)))) (existintro x xvar (ident (∃x α ⇒ α) xvar) (assume (∃x α ⇒ α))))
IP⊃HE : IP ∷ [] ⊃ HE
IP⊃HE (⊢IP ∷ []) (α ∷ []) = ip→he (descheme₂ ⊢IP) α


lem→glpo : ⊢₁ lem → ⊢₁ glpo
lem→glpo ⊢lem α = close
                   ((∅ ∪ (∃x α ~ ([ refl ] -∷ ∅))) ∪  (¬∃x α ~ (α ~ (((α ∷ [ refl ]) -∷ ∅) ∪ ([ refl ] -∷ ∅)))))
                   (disjelim
                    (cite "LEM" (⊢lem (∃x α)))
                    (disjintro₂ (∀x¬ α)
                     (assume (∃x α)))
                    (disjintro₁ (∃x α)
                     (univintro xvar (α ~ (((V∣ xvar α ⇒ atom []) ∷ ∅) ∪ ([ refl ] -∷ ∅)))
                      (arrowintro α
                       (arrowelim
                        (assume (¬∃x α))
                        (existintro x xvar (ident α xvar)
                         (assume α)))))))
LEM⊃GLPO : LEM ∷ [] ⊃ GLPO
LEM⊃GLPO (⊢LEM ∷ []) (α ∷ []) = lem→glpo (descheme₁ ⊢LEM) α

glpo→lem : ⊢₁ glpo → ⊢₁ lem
glpo→lem ⊢glpo α = close
                    (∅ ∪ ∀x¬ αω ~ [ refl ] -∷ ∅ ∪ ∃x αω ~ ([ refl ] -∷ ∅ ∪ αω ~ [ refl ] -∷ ∅))
                    (univelim x αω∨¬αω[ω/x]≡α∨¬α
                     (univintro ω (∅ ∪ ∀x¬ αω ~ [ refl ] -∷ ∅ ∪ ∃x αω ~ ([ refl ] -∷ ∅ ∪ αω ~ [ refl ] -∷ ∅))
                      (disjelim
                       (cite "GLPO" (⊢glpo αω))
                       (disjintro₂ αω
                        (univelim x (ident (¬ αω) xvar)
                         (assume (∀x (¬ αω)))))
                       (disjintro₁ (¬ αω)
                        (existelim (xαωnf ∷ αω ~ [ refl ] -∷ ∅)
                         (assume (∃x αω))
                         (assume αω))))))
                   where
                    ωfresh : FreshVar α xvar (varterm xvar)
                    ωfresh = freshVar α xvar x
                    ω : Variable
                    ω = FreshVar.var ωfresh
                    ωnf : ω NotFreeIn α
                    ωnf = FreshVar.notFree ωfresh
                    αω : Formula
                    αω = fst (α [ xvar / varterm ω ])
                    αωpf : α [ xvar / varterm ω ]≡ αω
                    αωpf = snd (α [ xvar / varterm ω ])
                    xαωnf : xvar NotFreeIn αω
                    xαωnf = repNotFree (varterm (FreshVar.new ωfresh)) αωpf
                    αω∨¬αω[ω/x]≡α∨¬α : (αω ∨ ¬ αω)[ ω / x ]≡ (α ∨ ¬ α)
                    αω∨¬αω[ω/x]≡α∨¬α = inverse ωnf αωpf ∨ (inverse ωnf αωpf ⇒ atom ⊥rel [])

GLPO⊃LEM : GLPO ∷ [] ⊃ LEM
GLPO⊃LEM (⊢GLPO ∷ []) (α ∷ []) = glpo→lem (descheme₁ ⊢GLPO) α

dp→gmp : ⊢₁ dp → ⊢₁ gmp
dp→gmp ⊢dp α = close
                ((Λ (mkvar zero) α ⇒ atom (mkrel zero zero) []) ~  (∅ ∪   ((α ⇒ Λ (mkvar zero) α) ~ (α ~  (((α ∷ ((α ⇒ Λ (mkvar zero) α) ∷ List.[ refl ])) -∷ ∅) ∪   (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅)))))))
                (arrowintro (¬∀x α)
                 (existelim (V∣ (mkvar zero) (α ⇒ atom (mkrel zero zero) []) ∷  ((α ⇒ Λ (mkvar zero) α) ~   (α ~(((Λ∣ (mkvar zero) α ⇒ atom []) ∷ ∅) ∪ (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅))))))
                  (cite "DP" (⊢dp α))
                  (existintro x xvar (ident (¬ α) xvar)
                   (arrowintro α
                    (arrowelim
                     (assume (¬∀x α))
                     (arrowelim
                      (assume (α ⇒ ∀x α))
                      (assume α)))))))
DP⊃GMP : DP ∷ [] ⊃ GMP
DP⊃GMP (⊢DP ∷ []) (α ∷ []) = dp→gmp (descheme₁ ⊢DP) α


dp→lpo : ⊢₁ dp → ⊢₂ lpo
dp→lpo ⊢dp α β = close
                  (∀x (α ∨ β) ~  (∅ ∪   ((α ⇒ ∀x α) ~(((((α ⇒ ∀x α) ∷ [ refl ]) -∷ ∅) ∪  (α ~ (((α ∷ [ refl ]) -∷ ∅) ∪ ([ refl ] -∷ ∅)))) ∪ (β ~ ([ refl ] -∷ ∅))))))
                  (arrowintro (∀x (α ∨ β))
                   (existelim
                    ((Λ∣ xvar α ∨ V∣ xvar β) ∷  ((α ⇒ ∀x α) ~   (((Λ∣ xvar (α ∨ β) ∷ ∅) ∪ (α ~ (((α ∷ [ refl ]) -∷ ∅) ∪ ([ refl ] -∷ ∅))))∪ (β ~ ([ refl ] -∷ ∅)))))
                    (cite "DP" (⊢dp α))
                    (disjelim
                     (univelim x (ident (α ∨ β) xvar)
                      (assume (∀x (α ∨ β))))
                     (disjintro₁ (∃x β)
                      (arrowelim
                       (assume (α ⇒ ∀x α))
                       (assume α)))
                     (disjintro₂ (∀x α)
                      (existintro x xvar (ident β xvar)
                       (assume β))))))
DP⊃LPO : DP ∷ [] ⊃ LPO
DP⊃LPO (⊢DP ∷ []) (α ∷ β ∷ []) = dp→lpo (descheme₁ ⊢DP) α β


dp→cd : ⊢₁ dp → ⊢₂ cd
dp→cd ⊢dp α β = close
                 (∀x (α ∨ ∃x β) ~ (∅ ∪ α ⇒ ∀x α ~ ((α ⇒ ∀x α ∷ [ refl ]) -∷ ∅ ∪ α ~ ((α ∷ [ refl ]) -∷ ∅ ∪ [ refl ] -∷ ∅) ∪ ∃x β ~ [ refl ] -∷ ∅)))
                 (arrowintro (∀x (α ∨ ∃x β))
                  (existelim (Λ∣ xvar α ∨ V∣ xvar β ∷ α ⇒ ∀x α ~ (Λ∣ xvar (α ∨ ∃x β) ∷ ∅ ∪ α ~ ((α ∷ [ refl ]) -∷ ∅ ∪ [ refl ] -∷ ∅) ∪ ∃x β ~ V∣ xvar β ∷ ∅))
                   (cite "DP" (⊢dp α))
                   (disjelim
                    (univelim x (ident (α ∨ ∃x β) xvar)
                     (assume (∀x (α ∨ ∃x β))))
                    (disjintro₁ (∃x β) (arrowelim (assume (α ⇒ ∀x α)) (assume α)))
                    (disjintro₂ (∀x α) (assume (∃x β))))))

DP⊃CD : DP ∷ [] ⊃ CD
DP⊃CD (⊢DP ∷ []) (α ∷ β ∷ []) = dp→cd (descheme₁ ⊢DP) α β
