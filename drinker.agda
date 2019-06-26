open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Sigma

open import Decidable hiding (⊥ ; ¬_)
open import Deduction
open import Ensemble
open import Formula
open import List
open import Scheme
open import Sugar
open import Texify
open import Vec

constFreeFor : ∀ α x n → functerm (func n zero) [] FreeFor x In α
constFreeFor (atom r ts) x n = atom r ts
constFreeFor (α ⇒ β) x n = constFreeFor α x n ⇒ constFreeFor β x n
constFreeFor (α ∧ β) x n = constFreeFor α x n ∧ constFreeFor β x n
constFreeFor (α ∨ β) x n = constFreeFor α x n ∨ constFreeFor β x n
constFreeFor (Λ x₁ α) x n = Λ (functerm []) (constFreeFor α x n)
constFreeFor (V x₁ α) x n = V (functerm []) (constFreeFor α x n)

LPO DNE EFQ LEM WLEM DGP GLPO GLPO′ GMP WGMP DP Hε DNS∀ DNS∃ IP CD : Scheme


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

LEM  = unaryscheme "LEM"  lem
WLEM = unaryscheme "WLEM" wlem


dgp : Formula → Formula → Formula
dgp Φ Ψ  = (Φ ⇒ Ψ) ∨ (Ψ ⇒ Φ)

DGP = binaryscheme "DGP" dgp


∃lem ∃wlem : Formula → Formula
∃lem  Φ = ∃x (lem Φ)
∃wlem Φ = ∃x (wlem Φ)

∃dgp : Formula → Formula → Formula
∃dgp  Φ ψ = ∃x (dgp Φ ψ)


glpo glpoa gmp wgmp : Formula → Formula
glpo  Φx = ∀x ¬Φx ∨ ∃x Φx                                       where ¬Φx = ¬ Φx
glpoa Φx = ∀x Φx ∨ ∃x ¬Φx                                       where ¬Φx = ¬ Φx
gmp   Φx = ¬∀x Φx ⇒ ∃x ¬Φx                                      where ¬Φx = ¬ Φx
wgmp  Φx = ¬∀x Φx ⇒ ¬¬(∃x ¬Φx)                                  where ¬Φx = ¬ Φx

GLPO  = unaryscheme "GLPO"  glpo
GLPO′ = unaryscheme "GLPO'" glpoa
GMP   = unaryscheme "GMP"   gmp
WGMP  = unaryscheme "WGMP"  wgmp



dp hε : Formula → Formula
dp  Φx = ∃x(Φx ⇒ ∀x Φx)
hε  Φx = ∃x(∃x Φx ⇒ Φx)

DP  = unaryscheme "DP" dp
Hε  = unaryscheme "H$\\epsilon$" hε



dns∀ dns∃ : Formula → Formula
dns∀ Φx = ∀x(¬¬ Φx) ⇒ ¬¬(∀x Φx)
dns∃ Φx = ¬¬(∃x Φx) ⇒ ∃x (¬¬ Φx)

DNS∀ = unaryscheme "DNS$\\forall$" dns∀
DNS∃ = unaryscheme "DNS$\\exists$" dns∃



-- These are usually stated with Ψ instead of ∃x Ψ, but this is a simple way of
-- adding bounded variable requirements as x is certainly not free in ∃x Ψ.
-- If x is in fact not free in Ψ, then the existential can be eliminated
-- separately.
cd ip : Formula → Formula → Formula
cd Φx Ψ = ∀x (Φx ∨ ∃x Ψ) ⇒ ∀x Φx ∨ ∃x Ψ
ip Φx Ψ = (∃x Ψ ⇒ ∃x Φx) ⇒ ∃x(∃x Ψ ⇒ Φx)

CD = binaryscheme "CD" cd
IP = binaryscheme "IP" ip

pattern ¬D t = ¬(D t)

d0 ¬d1 d∀ : Formula
d0 = D t0
¬d1 = ¬D t1
d∀ = ∀x (D x ∨ ¬D x)

D0 ¬D1 D∀ : Scheme
D0  = nullaryscheme "D$0$"         d0
¬D1 = nullaryscheme "$\\lnot$D$1$" ¬d1
D∀  = nullaryscheme "D$\\forall$"  d∀

TT : List Scheme
TT = D0 ∷ ¬D1 ∷ D∀ ∷ []



⊥c-rule : Set₁
⊥c-rule = ∀{Γ} → ∀ α
         →      Γ ⊢ ⊥
           --------------- ⊥c
         →  Γ - (¬ α) ⊢ α

⊥i-rule : Set₁
⊥i-rule = ∀{Γ} → ∀ α
         →      Γ ⊢ ⊥
               ------- ⊥i
         →      Γ ⊢ α

dne→⊥c-rule : ⊢₁ dne → ⊥c-rule
dne→⊥c-rule ⊢dne α Γ⊢⊥ = close
                          (assembled-context (arrowintro (¬ α) Γ⊢⊥))
                          (λ x₁ z₁ z₂ → z₂ (λ z₃ → z₁ (λ z₄ → z₄) (λ z₄ → z₄ z₃)))
                          (arrowelim
                           (⊢dne α)
                           (arrowintro (¬ α)
                            Γ⊢⊥))

⊥c-rule→dne : ⊥c-rule → ⊢₁ dne
⊥c-rule→dne ⊢⊥c-rule α = close
                          from∅
                          (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₃ z₅))))
                          (arrowintro (¬¬ α)
                           (⊢⊥c-rule α
                            (arrowelim
                             (assume (¬¬ α))
                             (assume (¬ α)))))

efq→⊥i-rule : ⊢₁ efq → ⊥i-rule
efq→⊥i-rule ⊢efq α Γ⊢⊥ = close
                          (assembled-context Γ⊢⊥)
                          (λ x₁ z₁ → z₁ (λ z₂ → z₂))
                          (arrowelim
                           (⊢efq α)
                           Γ⊢⊥)

⊥i-rule→dne : ⊥i-rule → ⊢₁ efq
⊥i-rule→dne ⊢⊥i-rule α = close
                          from∅
                          (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃)))
                          (arrowintro ⊥
                           (⊢⊥i-rule α
                            (assume ⊥)))




dne→lem : ⊢₁ dne → ⊢₁ lem
dne→lem ⊢dne α = close from∅
                  (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃)  (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄ (λ z₆ → z₆ (λ z₇ z₈ → z₈ z₄ z₇))))))
                  (arrowelim
                   (⊢dne (α ∨ ¬ α))
                   (arrowintro (¬ (α ∨ ¬ α))
                    (arrowelim
                     (assume (¬ (α ∨ ¬ α)))
                     (disjintro₂ α
                      (arrowintro α
                       (arrowelim
                        (assume (¬ (α ∨ ¬ α)))
                        (disjintro₁ (¬ α)
                         (assume α))))))))
DNE⊃LEM : DNE List.∷ [] ⊃ LEM
DNE⊃LEM ⊢lhs (α Vec.∷ []) = dne→lem (descheme₁ (⊢lhs DNE [ refl ])) α


dne→efq : ⊢₁ dne → ⊢₁ efq
dne→efq ⊢dne α = close from∅
                  (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ _ → z₃)))))
                  (arrowintro ⊥
                   (arrowelim
                    (⊢dne α)
                    (arrowintro (¬ α)
                     (assume ⊥))))
DNE⊃EFQ : DNE ∷ [] ⊃ EFQ
DNE⊃EFQ ⊢lhs (α ∷ []) = dne→efq (descheme₁ (⊢lhs DNE [ refl ])) α

lem,efq→dne : ⊢₁ lem → ⊢₁ efq → ⊢₁ dne
lem,efq→dne ⊢lem ⊢efq α = close from∅
                           (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ → z₆ (λ z₇ → z₇)) (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ z₉ → z₉) (λ z₉ → z₉ z₃ z₇)))))))
                           (arrowintro (¬¬ α)
                            (disjelim
                             (⊢lem α)
                             (assume α)
                             (arrowelim
                              (⊢efq α)
                              (arrowelim
                               (assume (¬¬ α))
                               (assume (¬ α))))))
LEM,EFQ⊃DNE : LEM ∷ EFQ ∷ [] ⊃ DNE
LEM,EFQ⊃DNE ⊢lhs (α ∷ []) = lem,efq→dne (descheme₁ (⊢lhs LEM [ refl ])) (descheme₁ (⊢lhs EFQ (_ ∷ [ refl ]))) α


hε→ip : ⊢₁ hε → ⊢₂ ip
hε→ip ⊢hε α β = close from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁  (λ z₃ z₄ →  z₄ (λ z₅ → z₅)  (λ z₅ → z₅ (λ z₆ z₇ → z₇ (λ z₈ z₉ → z₉ z₆ (λ z₁₀ → z₁₀ z₃ z₈)))))))
                 (arrowintro (∃x β ⇒ ∃x α)
                  (existelim
                   (all⟨ V↓ xvar (∃x β ⇒ α) ⟩ all∪ (all- (all- (all⟨- ∃x β ∷ [ refl ] ⟩ all∪ all⟨ V↓ xvar β ⇒ V↓ xvar α ⟩ all∪ all⟨ V↓ xvar β ⟩))))
                   (⊢hε α)
                   (existintro x xvar
                    (ident (∃x β ⇒ α) xvar)
                    (arrowintro (∃x β)
                    (arrowelim
                     (assume (∃x α ⇒ α))
                     (arrowelim
                      (assume (∃x β ⇒ ∃x α))
                      (assume (∃x β))))))))
Hε⊃IP : Hε ∷ [] ⊃ IP
Hε⊃IP ⊢lhs (α ∷ β ∷ []) = hε→ip (descheme₁ (⊢lhs Hε [ refl ])) α β


ip→hε : ⊢₂ ip → ⊢₁ hε
ip→hε ⊢ip α = close from∅
               (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃ (λ z₄ → z₄) (λ z₄ → z₄ (λ z₅ → z₅)))  (λ z₃ → z₃ (λ z₄ → z₄))))
               (existelim
                (all⟨ V↓ xvar (∃x α ⇒ α) ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                (arrowelim
                 (⊢ip α α)
                 (arrowintro (∃x α)
                  (assume (∃x α))))
                (existintro x xvar
                 (ident (∃x α ⇒ α) xvar)
                 (assume (∃x α ⇒ α))))
IP⊃Hε : IP ∷ [] ⊃ Hε
IP⊃Hε ⊢lhs (α ∷ []) = ip→hε (descheme₂ (⊢lhs IP [ refl ])) α


lem→glpo : ⊢₁ lem → ⊢₁ glpo
lem→glpo ⊢lem α = close from∅
                   (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃)  (λ z₃ →  z₃ (λ z₄ → z₄ (λ z₅ → z₅))  (λ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ z₈ → z₈ z₅ z₇))))))
                   (disjelim
                    (⊢lem (∃x α))
                    (disjintro₂ (∀x¬ α)
                     (assume (∃x α)))
                    (disjintro₁ (∃x α)
                     (univintro xvar
                      (all- (all⟨ V↓ xvar α ⇒ atom [] ⟩ all∪ all⟨- [ refl ] ⟩))
                      (arrowintro α
                       (arrowelim
                        (assume (¬∃x α))
                        (existintro x xvar (ident α xvar)
                         (assume α)))))))
LEM⊃GLPO : LEM ∷ [] ⊃ GLPO
LEM⊃GLPO ⊢lhs (α ∷ []) = lem→glpo (descheme₁ (⊢lhs LEM [ refl ])) α


∃lem→lem : ⊢₁ ∃lem → ⊢₁ lem
∃lem→lem ⊢∃lem α = close
                    from∅
                    (λ x₁ z z₁ → z₁ (z (λ z₂ → z₂) (λ z₂ → z₂ (λ z₃ → z₃))))
                    (univelim x lemαω[ω/x]≡lemα
                     (univintro ωvar (all∅ all∪ (all- all⟨- [ refl ] ⟩))
                      (existelim (all⟨ x∉αω ∨ (x∉αω ⇒ atom []) ⟩
                                  all∪ (all- all⟨- [ refl ] ⟩))
                       (⊢∃lem αω)
                       (assume (lem αω)))))
  where
    ω,ωFresh,x≢ω : Σ Variable (λ ω → Σ (ω FreshIn α) (λ _ → xvar ≢ ω))
    ω,ωFresh,x≢ω with fresh (∃x α)
    ω,ωFresh,x≢ω | ω , V x≢ω ωfrα = ω , ωfrα , x≢ω
    ωvar          : Variable
    ω∉α           : ωvar NotFreeIn α
    ωFreeForxInα  : (varterm ωvar) FreeFor xvar In α
    x≢ω           : xvar ≢ ωvar
    ωvar          = fst ω,ωFresh,x≢ω
    ω∉α           = freshNotFree (fst (snd ω,ωFresh,x≢ω))
    ωFreeForxInα  = freshFreeFor (fst (snd ω,ωFresh,x≢ω)) xvar
    x≢ω           = snd (snd ω,ωFresh,x≢ω)
    αω        : Formula
    α[x/ω]≡αω : α [ xvar / _ ]≡ αω
    αω        = fst (α [ xvar / ωFreeForxInα ])
    α[x/ω]≡αω = snd (α [ xvar / ωFreeForxInα ])
    lemαω[ω/x]≡lemα : (lem αω) [ ωvar / _ ]≡ (lem α)
    lemαω[ω/x]≡lemα = subInverse
                       (ω∉α ∨ (ω∉α ⇒ atom []))
                       (α[x/ω]≡αω ∨ (α[x/ω]≡αω ⇒ notfree (atom [])))
    x∉αω : xvar NotFreeIn αω
    x∉αω = subNotFree (varterm x≢ω) α[x/ω]≡αω
    x∉lemαω : xvar NotFreeIn (lem αω)
    x∉lemαω = x∉αω ∨ (x∉αω ⇒ atom [])

∃wlem→wlem : ⊢₁ ∃wlem → ⊢₁ wlem
∃wlem→wlem ⊢∃wlem α with xvar notFreeIn α
... | yes x∉α = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄))))
                 (existelim (all⟨ (x∉α ⇒ atom []) ∨ ((x∉α ⇒ atom []) ⇒ atom []) ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                  (⊢∃wlem α)
                  (assume (wlem α)))
... | no ¬x∉α = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄))))
                 (univelim x wlemαω[ω/x]≡wlemα
                  (univintro ωvar (all∅ all∪ (all- all⟨- [ refl ] ⟩))
                   (existelim (all⟨ x∉wlemαω ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                    (⊢∃wlem αω)
                    (assume (wlem αω)))))
      where
        ωvar : Variable
        ωvar = fst (fresh α)
        ωfresh : ωvar FreshIn α
        ωfresh = snd (fresh α)
        ω∉α : ωvar NotFreeIn α
        ω∉α = freshNotFree ωfresh
        ≡ω∉α : ∀ v → v ≡ ωvar → v NotFreeIn α
        ≡ω∉α v refl = ω∉α
        αω : Formula
        αω = fst (α [ xvar / freshFreeFor ωfresh xvar ])
        α[x/ω]≡αω : α [ xvar / _ ]≡ αω
        α[x/ω]≡αω = snd (α [ xvar / freshFreeFor ωfresh xvar ])
        wlemαω[ω/x]≡wlemα : (wlem αω) [ ωvar / _ ]≡ (wlem α)
        wlemαω[ω/x]≡wlemα = subInverse
                             ((ω∉α ⇒ atom []) ∨ ((ω∉α ⇒ atom []) ⇒ atom []))
                             ((α[x/ω]≡αω ⇒ notfree (atom []))
                              ∨ ((α[x/ω]≡αω ⇒ notfree (atom []))
                                 ⇒ notfree (atom [])))
        x∉αω : xvar NotFreeIn αω
        x∉αω = subNotFree (varterm λ x≡ω → ¬x∉α (≡ω∉α xvar x≡ω)) α[x/ω]≡αω
        x∉wlemαω : xvar NotFreeIn (wlem αω)
        x∉wlemαω = (x∉αω ⇒ atom []) ∨ ((x∉αω ⇒ atom []) ⇒ atom [])

∃dgp→dgp : ⊢₂ ∃dgp → ⊢₂ dgp
∃dgp→dgp ⊢∃dgp α β with xvar notFreeIn α | xvar notFreeIn β
... | yes x∉α | yes x∉β = close
                           from∅
                           (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄))))
                           (existelim (all⟨ (x∉α ⇒ x∉β) ∨ (x∉β ⇒ x∉α) ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                            (⊢∃dgp α β)
                            (assume (dgp α β)))
... | _       | no ¬x∉β = close
                           from∅
                           (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄))))
                           (univelim x dgpαωβω[ω/x]≡dgpαβ
                            (univintro ωvar (all∅ all∪ (all- all⟨- [ refl ] ⟩))
                             (existelim (all⟨ x∉dgpαωβω ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                              (⊢∃dgp αω βω)
                              (assume (dgp αω βω)))))
                where
                  ωvar : Variable
                  ωvar = fst (fresh (α ⇒ β))
                  ωfreshα : ωvar FreshIn α
                  ωfreshα with snd (fresh (α ⇒ β))
                  ... | frα ⇒ frβ = frα
                  ωfreshβ : ωvar FreshIn β
                  ωfreshβ with snd (fresh (α ⇒ β))
                  ... | frα ⇒ frβ = frβ
                  ω∉α : ωvar NotFreeIn α
                  ω∉α = freshNotFree ωfreshα
                  ω∉β : ωvar NotFreeIn β
                  ω∉β = freshNotFree ωfreshβ
                  ≡ω∉α : ∀ v → v ≡ ωvar → v NotFreeIn α
                  ≡ω∉α v refl = ω∉α
                  ≡ω∉β : ∀ v → v ≡ ωvar → v NotFreeIn β
                  ≡ω∉β v refl = ω∉β
                  αω : Formula
                  αω = fst (α [ xvar / freshFreeFor ωfreshα xvar ])
                  βω : Formula
                  βω = fst (β [ xvar / freshFreeFor ωfreshβ xvar ])
                  α[x/ω]≡αω : α [ xvar / _ ]≡ αω
                  α[x/ω]≡αω = snd (α [ xvar / freshFreeFor ωfreshα xvar ])
                  β[x/ω]≡βω : β [ xvar / _ ]≡ βω
                  β[x/ω]≡βω = snd (β [ xvar / freshFreeFor ωfreshβ xvar ])
                  dgpαωβω[ω/x]≡dgpαβ : (dgp αω βω) [ ωvar / _ ]≡ (dgp α β)
                  dgpαωβω[ω/x]≡dgpαβ = subInverse
                                        ((ω∉α ⇒ ω∉β) ∨ (ω∉β ⇒ ω∉α))
                                        ((α[x/ω]≡αω ⇒ β[x/ω]≡βω)
                                         ∨ (β[x/ω]≡βω ⇒ α[x/ω]≡αω))
                  x∉αω : xvar NotFreeIn αω
                  x∉αω = subNotFree (varterm λ x≡ω → ¬x∉β (≡ω∉β xvar x≡ω)) α[x/ω]≡αω
                  x∉βω : xvar NotFreeIn βω
                  x∉βω = subNotFree (varterm λ x≡ω → ¬x∉β (≡ω∉β xvar x≡ω)) β[x/ω]≡βω
                  x∉dgpαωβω : xvar NotFreeIn (dgp αω βω)
                  x∉dgpαωβω = (x∉αω ⇒ x∉βω) ∨ (x∉βω ⇒ x∉αω)
... | no ¬x∉α | _       = close
                           from∅
                           (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄))))
                           (univelim x dgpαωβω[ω/x]≡dgpαβ
                            (univintro ωvar (all∅ all∪ (all- all⟨- [ refl ] ⟩))
                             (existelim (all⟨ x∉dgpαωβω ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                              (⊢∃dgp αω βω)
                              (assume (dgp αω βω)))))
                where
                  ωvar : Variable
                  ωvar = fst (fresh (α ⇒ β))
                  ωfreshα : ωvar FreshIn α
                  ωfreshα with snd (fresh (α ⇒ β))
                  ... | frα ⇒ frβ = frα
                  ωfreshβ : ωvar FreshIn β
                  ωfreshβ with snd (fresh (α ⇒ β))
                  ... | frα ⇒ frβ = frβ
                  ω∉α : ωvar NotFreeIn α
                  ω∉α = freshNotFree ωfreshα
                  ω∉β : ωvar NotFreeIn β
                  ω∉β = freshNotFree ωfreshβ
                  ≡ω∉α : ∀ v → v ≡ ωvar → v NotFreeIn α
                  ≡ω∉α v refl = ω∉α
                  ≡ω∉β : ∀ v → v ≡ ωvar → v NotFreeIn β
                  ≡ω∉β v refl = ω∉β
                  αω : Formula
                  αω = fst (α [ xvar / freshFreeFor ωfreshα xvar ])
                  βω : Formula
                  βω = fst (β [ xvar / freshFreeFor ωfreshβ xvar ])
                  α[x/ω]≡αω : α [ xvar / _ ]≡ αω
                  α[x/ω]≡αω = snd (α [ xvar / freshFreeFor ωfreshα xvar ])
                  β[x/ω]≡βω : β [ xvar / _ ]≡ βω
                  β[x/ω]≡βω = snd (β [ xvar / freshFreeFor ωfreshβ xvar ])
                  dgpαωβω[ω/x]≡dgpαβ : (dgp αω βω) [ ωvar / _ ]≡ (dgp α β)
                  dgpαωβω[ω/x]≡dgpαβ = subInverse
                                        ((ω∉α ⇒ ω∉β) ∨ (ω∉β ⇒ ω∉α))
                                        ((α[x/ω]≡αω ⇒ β[x/ω]≡βω)
                                         ∨ (β[x/ω]≡βω ⇒ α[x/ω]≡αω))
                  x∉αω : xvar NotFreeIn αω
                  x∉αω = subNotFree (varterm λ x≡ω → ¬x∉α (≡ω∉α xvar x≡ω)) α[x/ω]≡αω
                  x∉βω : xvar NotFreeIn βω
                  x∉βω = subNotFree (varterm λ x≡ω → ¬x∉α (≡ω∉α xvar x≡ω)) β[x/ω]≡βω
                  x∉dgpαωβω : xvar NotFreeIn (dgp αω βω)
                  x∉dgpαωβω = (x∉αω ⇒ x∉βω) ∨ (x∉βω ⇒ x∉αω)


glpo→∃lem : ⊢₁ glpo → ⊢₁ ∃lem
glpo→∃lem ⊢glpo α = close
                     from∅
                     (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄ (λ z₅ → z₅)) (λ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ (λ z₇ → z₇ (λ z₈ → z₈)))))))
                     (disjelim
                       (⊢glpo α)
                       (existintro x xvar (ident (α ∨ ¬ α) xvar)
                       (disjintro₂ α
                         (univelim x (ident (¬ α) xvar)
                         (assume (∀x¬ α)))))
                       (existelim (all⟨ V↓ xvar (α ∨ ¬ α) ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                       (assume (∃x α))
                       (existintro x xvar (ident (α ∨ ¬ α) xvar)
                         (disjintro₁ (¬ α)
                         (assume α)))))

--glpo→lem : ⊢₁ glpo → ⊢₁ lem
--glpo→lem ⊢glpo α = ∃lem→lem (glpo→∃lem ⊢glpo) α

wlog-lem : (∀ α → xvar NotFreeIn α → ⊢ (lem α)) → ⊢₁ lem
wlog-lem ⊢nflem α = close
                     from∅
                     (λ x₁ z₁ z₂ → z₂ z₁)
                     (univelim x lemαω[ω/x]≡lemα
                      (univintro ωvar all∅
                       (⊢nflem αω x∉αω)))
  where
    ω,ωFresh,x≢ω : Σ Variable (λ ω → Σ (ω FreshIn α) (λ _ → xvar ≢ ω))
    ω,ωFresh,x≢ω with fresh (∀x α)
    ω,ωFresh,x≢ω | ω , Λ x≢ω ωFrα = ω , ωFrα , x≢ω
    ωvar          : Variable
    ω∉α           : ωvar NotFreeIn α
    ωFreeForxInα  : (varterm ωvar) FreeFor xvar In α
    x≢ω           : xvar ≢ ωvar
    ωvar          = fst ω,ωFresh,x≢ω
    ω∉α           = freshNotFree (fst (snd ω,ωFresh,x≢ω))
    ωFreeForxInα  = freshFreeFor (fst (snd ω,ωFresh,x≢ω)) xvar
    x≢ω           = snd (snd ω,ωFresh,x≢ω)
    αω        : Formula
    α[x/ω]≡αω : α [ xvar / _ ]≡ αω
    αω        = fst (α [ xvar / ωFreeForxInα ])
    α[x/ω]≡αω = snd (α [ xvar / ωFreeForxInα ])
    lemαω[ω/x]≡lemα : (lem αω) [ ωvar / _ ]≡ (lem α)
    lemαω[ω/x]≡lemα = subInverse
                         (ω∉α ∨ (ω∉α ⇒ atom []))
                         (α[x/ω]≡αω ∨ (α[x/ω]≡αω ⇒ notfree (atom [])))
    x∉αω : xvar NotFreeIn αω
    x∉αω = subNotFree (varterm x≢ω) α[x/ω]≡αω

glpo→rlem : ⊢₁ glpo → ∀ α → xvar NotFreeIn α → ⊢ (lem α)
glpo→rlem ⊢glpo α x∉α = close
                         from∅
                         (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄ (λ z₅ → z₅)) (λ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ (λ z₇ → z₇ (λ z₈ → z₈)))))))
                         (disjelim
                          (⊢glpo α)
                          (disjintro₂ α
                           (univelim x (ident (¬ α) xvar)
                            (assume (∀x¬ α))))
                          (disjintro₁ (¬ α)
                           (existelim (all⟨ x∉α ⟩ all∪ (all- all⟨ x∉α ⟩))
                            (assume (∃x α))
                            (assume α))))

glpo→lem : ⊢₁ glpo → ⊢₁ lem
glpo→lem ⊢glpo = wlog-lem (glpo→rlem ⊢glpo)
GLPO⊃LEM : GLPO ∷ [] ⊃ LEM
GLPO⊃LEM ⊢lhs (α ∷ []) = glpo→lem (descheme₁ (⊢lhs GLPO [ refl ])) α

dns∀→wgmp : ⊢₁ dns∀ → ⊢₁ wgmp
dns∀→wgmp ⊢dns∀ α = close
                     from∅
                     (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ → z₇ (λ z₈ → z₈) (λ z₈ → z₈ (λ z₉ z₁₀ → z₁₀ z₅ z₉))) z₃))))
                     (arrowintro (¬∀x α)
                      (arrowintro (¬∃x¬ α)
                       (arrowelim
                        (arrowelim
                         (⊢dns∀ α)
                         (univintro xvar (all- (all⟨ V↓ xvar (¬ α) ⇒ atom [] ⟩ all∪ all⟨- [ refl ] ⟩))
                          (arrowintro (¬ α)
                           (arrowelim
                            (assume (¬∃x¬ α))
                            (existintro x xvar (ident (¬ α) xvar)
                             (assume (¬ α)))))))
                        (assume (¬∀x α)))))
DNS∀⊃WGMP : DNS∀ ∷ [] ⊃ WGMP
DNS∀⊃WGMP ⊢lhs (α ∷ []) = dns∀→wgmp (descheme₁ (⊢lhs DNS∀ [ refl ])) α

wgmp→dns∀ : ⊢₁ wgmp → ⊢₁ dns∀
wgmp→dns∀ ⊢wgmp α = close
                     from∅
                     (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ → z₇ (λ z₈ → z₈) z₅) (λ z₇ → z₇ (λ z₈ z₉ → z₉ z₈ (λ z₁₀ → z₁₀ (λ z₁₁ z₁₂ → z₁₂ z₃ z₁₁))))))))
                     (arrowintro (∀x¬¬ α)
                      (arrowintro (¬∀x α)
                       (arrowelim
                        (arrowelim
                         (⊢wgmp α)
                         (assume (¬∀x α)))
                        (arrowintro (∃x¬ α)
                         (existelim (all⟨ atom [] ⟩ all∪  (all- (all⟨ Λ↓ xvar (¬¬ α) ⟩ all∪ all⟨- [ refl ] ⟩)))
                          (assume (∃x¬ α))
                          (arrowelim
                           (univelim x (ident (¬¬ α) xvar)
                            (assume (∀x¬¬ α)))
                           (assume (¬ α))))))))
WGMP⊃DNS∀ : WGMP ∷ [] ⊃ DNS∀
WGMP⊃DNS∀ ⊢lhs (α ∷ []) = wgmp→dns∀ (descheme₁ (⊢lhs WGMP [ refl ])) α

--dp→dp′ : ⊢₁ dp → ∀ α ωvar → (ff : (varterm ωvar) FreeFor xvar In α) → ⊢ V ωvar (Λ xvar (fst (α [ xvar / ff ]) ⇒ α))
--dp→dp′ ⊢dp α ωvar ωffx = close {!   !} {!   !} (existelim {!   !} (⊢dp α) (existintro {!   !} {!   !} {!   !} {!   !}))

dne→dp : ⊢₁ dne → ⊢₁ dp
dne→dp ⊢dne α = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄ (λ z₆ → z₆ (λ _ z₇ → z₇ (λ z₈ → z₈) (λ z₈ → z₈ (λ z₉ z₁₀ → z₁₀ z₄ (λ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ (λ z₁₄ → z₁₄) (λ z₁₄ → z₁₄ (λ _ z₁₅ → z₁₅ z₉ z₁₂))))))))))))
                 (arrowelim
                  (⊢dne (dp α))
                  (arrowintro (¬ (dp α))
                   (arrowelim
                    (assume (¬ (dp α)))
                    (existintro x xvar (ident (α ⇒ ∀x α) xvar)
                     (arrowintro α
                      (univintro xvar (all∅ all∪ (all- (all⟨ V↓ xvar (α ⇒ ∀x α) ⇒ atom [] ⟩ all∪ (all- (all∅ all∪ (all- (all⟨- ¬∀x α ∷ (α ∷ [ refl ]) ⟩ all∪ all⟨- ¬∀x α ∷ [ refl ] ⟩)))))))
                       (arrowelim
                        (⊢dne α)
                        (arrowintro (¬ α)
                         (arrowelim
                          (assume (¬ (dp α)))
                          (existintro x xvar (ident (α ⇒ ∀x α) xvar)
                          (arrowintro α
                           (arrowelim
                            (⊢dne (∀x α))
                            (arrowintro (¬∀x α)
                             (arrowelim
                              (assume (¬ α))
                              (assume α)))))))))))))))
DNE⊃DP : DNE ∷ [] ⊃ DP
DNE⊃DP ⊢lhs (α ∷ []) = dne→dp (descheme₁ (⊢lhs DNE [ refl ])) α

dne→hε : ⊢₁ dne → ⊢₁ hε
dne→hε ⊢dne α = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄ (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ z₉ → z₉) (λ z₉ → z₉ (λ _ z₁₀ → z₁₀ z₇ (λ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ z₄ (λ z₁₄ → z₁₄ (λ _ → z₁₂))))))))))))
                 (arrowelim
                  (⊢dne (hε α))
                  (arrowintro (¬ (hε α))
                   (arrowelim
                    (assume (¬ (hε α)))
                    (existintro x xvar (ident (∃x α ⇒ α) xvar)
                     (arrowintro (∃x α)
                      (arrowelim
                       (⊢dne α)
                       (arrowintro (¬ α)
                        (existelim (all⟨ atom [] ⟩ all∪ (all- (all⟨ V↓ xvar (∃x α ⇒ α) ⇒ atom [] ⟩ all∪ (all- all⟨- ∃x α ∷ [ refl ] ⟩))))
                         (assume (∃x α))
                         (arrowelim
                          (assume (¬ (hε α)))
                          (existintro x xvar (ident (∃x α ⇒ α) xvar)
                           (arrowintro (∃x α)
                            (assume α))))))))))))
DNE⊃Hε : DNE ∷ [] ⊃ Hε
DNE⊃Hε ⊢lhs (α ∷ []) = dne→hε (descheme₁ (⊢lhs DNE [ refl ])) α


lem→wlem : ⊢₁ lem → ⊢₁ wlem
lem→wlem ⊢lem α = ⊢lem (¬ α)
LEM⊃WLEM : LEM ∷ [] ⊃ WLEM
LEM⊃WLEM ⊢lhs (α ∷ []) = lem→wlem (descheme₁ (⊢lhs LEM [ refl ])) α


gmp→wgmp : ⊢₁ gmp → ⊢₁ wgmp
gmp→wgmp ⊢gmp α = close
                   from∅
                   (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ (λ z₇ → z₇ (λ z₈ → z₈) z₃)))))
                   (arrowintro (¬∀x α)
                    (arrowintro (¬∃x¬ α)
                     (arrowelim
                      (assume (¬∃x¬ α))
                      (arrowelim
                       (⊢gmp α)
                       (assume (¬∀x α))))))
GMP⊃WGMP : GMP ∷ [] ⊃ WGMP
GMP⊃WGMP ⊢lhs (α ∷ []) = gmp→wgmp (descheme₁ (⊢lhs GMP [ refl ])) α


dgp→wlem : ⊢₂ dgp → ⊢₁ wlem
dgp→wlem ⊢dgp α = close
                   from∅
                   (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ z₈ → z₈ (λ z₉ → z₉ z₅ z₇) z₇))) (λ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ z₈ → z₈ z₇ (λ z₉ → z₉ z₅ z₇)))))))
                   (disjelim
                    (⊢dgp α (¬ α))
                    (disjintro₁ (¬¬ α)
                     (arrowintro α
                      (arrowelim
                       (arrowelim
                        (assume (α ⇒ ¬ α))
                        (assume α))
                       (assume α))))
                    (disjintro₂ (¬ α)
                     (arrowintro (¬ α)
                      (arrowelim
                       (assume (¬ α))
                       (arrowelim
                        (assume (¬ α ⇒ α))
                        (assume (¬ α)))))))
DGP⊃WLEM : DGP ∷ [] ⊃ WLEM
DGP⊃WLEM ⊢lhs (α ∷ []) = dgp→wlem (descheme₂ (⊢lhs DGP [ refl ])) α


glpoa→∃lem : ⊢₁ glpoa → ⊢₁ ∃lem
glpoa→∃lem ⊢glpoa α = close
                       from∅
                       (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄ (λ z₅ → z₅)) (λ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ (λ z₇ → z₇ (λ z₈ → z₈)))))))
                       (disjelim
                        (⊢glpoa α)
                        (existintro x xvar (ident (α ∨ ¬ α) xvar)
                         (disjintro₁ (¬ α)
                          (univelim x (ident α xvar)
                           (assume (∀x α)))))
                        (existelim (all⟨ V↓ xvar (α ∨ ¬ α) ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                         (assume (∃x¬ α))
                         (existintro x xvar (ident (α ∨ ¬ α) xvar)
                          (disjintro₂ α
                           (assume (¬ α))))))

glpoa→lem : ⊢₁ glpoa → ⊢₁ lem
glpoa→lem ⊢glpoa α = ∃lem→lem (glpoa→∃lem ⊢glpoa) α
GLPO′⊃LEM : GLPO′ ∷ [] ⊃ LEM
GLPO′⊃LEM ⊢lhs (α ∷ []) = glpoa→lem (descheme₁ (⊢lhs GLPO′ [ refl ])) α

glpoa→gmp : ⊢₁ glpoa → ⊢₁ gmp
glpoa→gmp ⊢glpoa α = close
                      from∅
                      (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ _ z₉ → z₉ z₃ z₇))) (λ z₆ → z₆ (λ z₇ → z₇))))))
                      (arrowintro (¬∀x α)
                       (disjelim
                        (⊢glpoa α)
                        (existintro x xvar (ident (¬ α) xvar)
                         (arrowintro α
                          (arrowelim
                           (assume (¬∀x α))
                           (assume (∀x α)))))
                        (assume (∃x¬ α))))
GLPO′⊃GMP : GLPO′ ∷ [] ⊃ GMP
GLPO′⊃GMP ⊢lhs (α ∷ []) = glpoa→gmp (descheme₁ (⊢lhs GLPO′ [ refl ])) α


dp→cd : ⊢₁ dp → ⊢₂ cd
dp→cd ⊢dp α β = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ z₃ (λ z₈ → z₈ (λ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₆ z₁₀)) (λ z₉ → z₉ (λ z₁₀ → z₁₀))))))))
                 (arrowintro (∀x (α ∨ ∃x β))
                  (existelim (all⟨ Λ↓ xvar α ∨ V↓ xvar β ⟩ all∪ (all- (all⟨ Λ↓ xvar (α ∨ ∃x β) ⟩ all∪ (all- (all⟨- α ∷ [ refl ] ⟩ all∪ all⟨- [ refl ] ⟩)) all∪ (all- all⟨ V↓ xvar β ⟩))))
                   (⊢dp α)
                   (disjelim
                    (univelim x (ident (α ∨ ∃x β) xvar)
                     (assume (∀x (α ∨ ∃x β))))
                    (disjintro₁ (∃x β) (arrowelim (assume (α ⇒ ∀x α)) (assume α)))
                    (disjintro₂ (∀x α) (assume (∃x β))))))
DP⊃CD : DP ∷ [] ⊃ CD
DP⊃CD ⊢lhs (α ∷ β ∷ []) = dp→cd (descheme₁ (⊢lhs DP [ refl ])) α β


dp→gmp : ⊢₁ dp → ⊢₁ gmp
dp→gmp ⊢dp α = close
                from∅
                (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ (λ z₈ z₉ → z₉ z₃ (λ z₁₀ → z₁₀ z₆ z₈)))))))
                (arrowintro (¬∀x α)
                 (existelim (all⟨ V↓ xvar (¬ α) ⟩ all∪ (all- (all- (all⟨ Λ↓ xvar α ⇒ atom [] ⟩ all∪ all⟨- α ∷ [ refl ] ⟩ all∪ all⟨- [ refl ] ⟩))))
                  (⊢dp α)
                  (existintro x xvar (ident (¬ α) xvar)
                   (arrowintro α
                    (arrowelim
                     (assume (¬∀x α))
                     (arrowelim
                      (assume (α ⇒ ∀x α))
                      (assume α)))))))
DP⊃GMP : DP ∷ [] ⊃ GMP
DP⊃GMP ⊢lhs (α ∷ []) = dp→gmp (descheme₁ (⊢lhs DP [ refl ])) α


hε→dns∃ : ⊢₁ hε → ⊢₁ dns∃
hε→dns∃ ⊢hε α = close
                   from∅
                   (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ (λ z₈ z₉ → z₉ z₃ (λ z₁₀ → z₁₀ (λ z₁₁ z₁₂ → z₁₂ z₈ (λ z₁₃ → z₁₃ z₆ z₁₁)))))))))
                   (arrowintro (¬¬∃x α)
                    (existelim (all⟨ V↓ xvar (¬¬ α) ⟩ all∪ (all- (all- (all⟨ (V↓ xvar α ⇒ atom []) ⇒ atom [] ⟩ all∪ (all- (all⟨- ∃x α ∷ [ refl ] ⟩ all∪ all⟨- ∃x α ∷ (¬ α ∷ [ refl ]) ⟩ all∪ all⟨ V↓ xvar α ⟩))))))
                     (⊢hε α)
                     (existintro x xvar (ident (¬¬ α) xvar)
                      (arrowintro (¬ α)
                       (arrowelim
                        (assume (¬¬∃x α))
                        (arrowintro (∃x α)
                         (arrowelim
                          (assume (¬ α))
                          (arrowelim
                           (assume (∃x α ⇒ α))
                           (assume (∃x α))))))))))
Hε⊃DNS∃ : Hε ∷ [] ⊃ DNS∃
Hε⊃DNS∃ ⊢lhs (α ∷ []) = hε→dns∃ (descheme₁ (⊢lhs Hε [ refl ])) α


glpo→dns∃ : ⊢₁ glpo → ⊢₁ dns∃
glpo→dns∃ ⊢glpo α = close
                   from∅
                   (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ _ z₉ → z₉ z₃ (λ z₁₀ → z₁₀ (λ z₁₁ z₁₂ → z₁₂ z₁₁ (λ z₁₃ → z₁₃ (λ z₁₄ z₁₅ → z₁₅ z₇ z₁₄))))))) (λ z₆ → z₆ (λ z₇ z₈ → z₈ z₇ (λ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ z₁₂ z₁₀)))))))))
                   (arrowintro (¬¬∃x α)
                    (disjelim
                     (⊢glpo α)
                     (existintro x xvar (ident (¬¬ α) xvar)
                      (arrowintro (¬ α)
                       (arrowelim
                        (assume (¬¬∃x α))
                        (arrowintro (∃x α)
                         (existelim (all⟨ atom [] ⟩ all∪  (all- (all⟨ Λ↓ xvar (¬ α) ⟩ all∪ all⟨- [ refl ] ⟩)))
                          (assume (∃x α))
                          (arrowelim
                           (univelim x (ident (¬ α) xvar)
                            (assume (∀x¬ α)))
                           (assume α)))))))
                     (existelim (all⟨ V↓ xvar (¬¬ α) ⟩ all∪ (all- (all- (all⟨- [ refl ] ⟩ all∪ all⟨- ¬ α ∷ [ refl ] ⟩))))
                      (assume (∃x α))
                      (existintro x xvar (ident (¬¬ α) xvar)
                       (arrowintro (¬ α)
                        (arrowelim
                         (assume (¬ α))
                         (assume α)))))))
GLPO⊃DNS∃ : GLPO ∷ [] ⊃ DNS∃
GLPO⊃DNS∃ ⊢lhs (α ∷ []) = glpo→dns∃ (descheme₁ (⊢lhs GLPO [ refl ])) α


gmp→dns∃ : ⊢₁ gmp → ⊢₁ dns∃
gmp→dns∃ ⊢gmp α = close
                   from∅
                   (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ z₃ (λ z₈ → z₈ (λ z₉ z₁₀ → z₁₀ z₉ (λ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ z₆ z₁₂)))))))))
                   (arrowintro (¬¬∃x α)
                    (arrowelim
                     (⊢gmp (¬ α))
                     (arrowintro (∀x¬ α)
                      (arrowelim
                       (assume (¬¬∃x α))
                       (arrowintro (∃x α)
                        (existelim (all⟨ atom [] ⟩ all∪ (all- (all⟨ Λ↓ xvar (¬ α) ⟩ all∪ all⟨- [ refl ] ⟩)))
                         (assume (∃x α))
                         (arrowelim
                          (univelim x (ident (¬ α) xvar)
                           (assume (∀x¬ α)))
                          (assume α))))))))
GMP⊃DNS∃ : GMP ∷ [] ⊃ DNS∃
GMP⊃DNS∃ ⊢lhs (α ∷ []) = gmp→dns∃ (descheme₁ (⊢lhs GMP [ refl ])) α


wlog-dgp : (∀ α β → xvar NotFreeIn α → xvar NotFreeIn β → ⊢ (dgp α β)) → ⊢₂ dgp
wlog-dgp ⊢nfdgp α β = close
                       from∅
                       (λ x₁ z₁ z₂ → z₂ z₁)
                       (univelim x dgpαωβω[ω/x]≡dgpαβ
                        (univintro ωvar all∅
                         (⊢nfdgp αω βω x∉αω x∉βω)))
  where
    ω,ωFresh,x≢ω : Σ Variable (λ ω → Σ (ω FreshIn α) (λ _ → Σ (ω FreshIn β) (λ _ → xvar ≢ ω)))
    ω,ωFresh,x≢ω with fresh (∀x (α ⇒ β))
    ω,ωFresh,x≢ω | ω , Λ x≢ω (ωFrα ⇒ ωFrβ) = ω , ωFrα , ωFrβ , x≢ω
    ωvar          : Variable
    ω∉α           : ωvar NotFreeIn α
    ω∉β           : ωvar NotFreeIn β
    ωFreeForxInα  : (varterm ωvar) FreeFor xvar In α
    ωFreeForxInβ  : (varterm ωvar) FreeFor xvar In β
    x≢ω           : xvar ≢ ωvar
    ωvar          = fst ω,ωFresh,x≢ω
    ω∉α           = freshNotFree (fst (snd ω,ωFresh,x≢ω))
    ω∉β           = freshNotFree (fst (snd (snd ω,ωFresh,x≢ω)))
    ωFreeForxInα  = freshFreeFor (fst (snd ω,ωFresh,x≢ω)) xvar
    ωFreeForxInβ  = freshFreeFor (fst (snd (snd ω,ωFresh,x≢ω))) xvar
    x≢ω           = snd (snd (snd ω,ωFresh,x≢ω))
    αω        : Formula
    α[x/ω]≡αω : α [ xvar / _ ]≡ αω
    αω        = fst (α [ xvar / ωFreeForxInα ])
    α[x/ω]≡αω = snd (α [ xvar / ωFreeForxInα ])
    βω        : Formula
    β[x/ω]≡βω : β [ xvar / _ ]≡ βω
    βω        = fst (β [ xvar / ωFreeForxInβ ])
    β[x/ω]≡βω = snd (β [ xvar / ωFreeForxInβ ])
    dgpαωβω[ω/x]≡dgpαβ : (dgp αω βω) [ ωvar / _ ]≡ (dgp α β)
    dgpαωβω[ω/x]≡dgpαβ = subInverse
                          ((ω∉α ⇒ ω∉β) ∨ (ω∉β ⇒ ω∉α))
                          ((α[x/ω]≡αω ⇒ β[x/ω]≡βω) ∨ (β[x/ω]≡βω ⇒ α[x/ω]≡αω))
    x∉αω : xvar NotFreeIn αω
    x∉αω = subNotFree (varterm x≢ω) α[x/ω]≡αω
    x∉βω : xvar NotFreeIn βω
    x∉βω = subNotFree (varterm x≢ω) β[x/ω]≡βω

dp,efq,tt→rdgp : ⊢₁ dp → ⊢₁ efq → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ∀ α β → xvar NotFreeIn α → xvar NotFreeIn β → ⊢ dgp α β
dp,efq,tt→rdgp ⊢dp ⊢efq ⊢d0 ⊢¬d1 ⊢d∀ α β x∉α x∉β =
    close
     from∅
     (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ z₅ → z₅ (λ z₆ → z₆) (λ z₆ → z₆ (λ z₇ → z₇ (λ z₈ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ (λ z₁₂ → z₁₂ z₄ (λ z₁₃ → z₁₃ (λ z₁₄ → z₁₄ (λ _ → z₁₀)) (λ z₁₄ → z₁₄ (λ z₁₅ z₁₆ → z₁₆ (λ z₁₇ → z₁₇) (λ z₁₇ → z₁₇ z₁₅ z₈))))) (λ z₁₂ → z₁₂ (λ z₁₃ z₁₄ → z₁₄ (λ _ z₁₅ → z₁₅ z₁₃ (λ z₁₆ → z₁₆))))))) (λ z₇ → z₇ (λ z₈ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ (λ z₁₂ → z₁₂ z₄ (λ z₁₃ → z₁₃ (λ z₁₄ → z₁₄ (λ z₁₅ z₁₆ → z₁₆ (λ z₁₇ → z₁₇) (λ z₁₇ → z₁₇ z₈ z₁₅))) (λ z₁₄ → z₁₄ (λ _ → z₁₀)))) (λ z₁₂ → z₁₂ (λ _ z₁₃ → z₁₃ (λ z₁₄ z₁₅ → z₁₅ z₁₄ (λ z₁₆ → z₁₆))))))))))))
     (existelim (all⟨ (x∉α ⇒ x∉β) ∨ (x∉β ⇒ x∉α) ⟩ all∪ (all- (all∅ all∪ (all- (all- ((all⟨- α ∷ (D x ∷ [ refl ]) ⟩ all∪ (all- all⟨ x∉α ⟩) all∪ (all- (all∅ all∪ all⟨- [ refl ] ⟩ all∪ all⟨- ¬D x ∷ (α ∷ [ refl ]) ⟩))) all∪ (all- (all- (all⟨- (D (functerm (func 1 zero) []) ⇒ α) ∷ [ refl ] ⟩ all∪ all∅)))))) all∪ (all- (all- ((all⟨- β ∷ (¬D x ∷ [ refl ]) ⟩ all∪ (all- (all∅ all∪ all⟨- D x ∷ (β ∷ [ refl ]) ⟩ all∪ all⟨- [ refl ] ⟩)) all∪ (all- all⟨ x∉β ⟩)) all∪ (all- (all- (all⟨- [ refl ] ⟩ all∪ all∅)))))))))
      (⊢dp φ)
      (disjelim
       (univelim x (ident (D x ∨ ¬D x) xvar)
        ⊢d∀)
       (disjintro₁ (β ⇒ α)
        (arrowintro α
         (conjelim
          (univelim t1 φ1sub
           (arrowelim
            (assume (φ ⇒ ∀x φ))
            (conjintro
             (arrowintro (D x)
              (assume α))
             (arrowintro (¬D x)
              (arrowelim
               (⊢efq β)
               (arrowelim
                (assume (¬D x))
                (assume (D x))))))))
          (arrowelim
           (assume (¬d1 ⇒ β))
           ⊢¬d1))))
       (disjintro₂ (α ⇒ β)
        (arrowintro β
         (conjelim
          (univelim t0 φ0sub
           (arrowelim
            (assume (φ ⇒ ∀x φ))
            (conjintro
             (arrowintro (D x)
              (arrowelim
               (⊢efq α)
               (arrowelim
                (assume (¬D x))
                (assume (D x)))))
             (arrowintro (¬D x)
              (assume β)))))
          (arrowelim
           (assume (d0 ⇒ α))
           ⊢d0))))))
  where
    φ : Formula
    φ = (D x ⇒ α) ∧ (¬D x ⇒ β)
    φ0sub : φ [ xvar / t0 ]≡ ((D t0 ⇒ α) ∧ (¬D t0 ⇒ β))
    φ0sub = (D varterm≡ ⇒ notfree x∉α) ∧ (¬D varterm≡ ⇒ notfree x∉β)
    φ1sub : φ [ xvar / t1 ]≡ ((D t1 ⇒ α) ∧ (¬D t1 ⇒ β))
    φ1sub = (D varterm≡ ⇒ notfree x∉α) ∧ (¬D varterm≡ ⇒ notfree x∉β)

dp,efq,tt→dgp : ⊢₁ dp → ⊢₁ efq → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ⊢₂ dgp
dp,efq,tt→dgp ⊢dp ⊢efq ⊢d0 ⊢¬d1 ⊢d∀ = wlog-dgp (dp,efq,tt→rdgp ⊢dp ⊢efq ⊢d0 ⊢¬d1 ⊢d∀)

DP,EFQ,TT⊃DGP : DP ∷ EFQ ∷ TT ⊃ DGP
DP,EFQ,TT⊃DGP ⊢lhs (α ∷ β ∷ []) =
    dp,efq,tt→dgp
     (descheme₁ (⊢lhs DP [ refl ]))
     (descheme₁ (⊢lhs EFQ (_ ∷ [ refl ])))
     (descheme₀ (⊢lhs D0 (_ ∷ (_ ∷ [ refl ]))))
     (descheme₀ (⊢lhs ¬D1 (_ ∷ (_ ∷ (_ ∷ [ refl ])))))
     (descheme₀ (⊢lhs D∀ (_ ∷ (_ ∷ (_ ∷ (_ ∷ [ refl ]))))))
     α
     β


hε,efq,tt→rdgp : ⊢₁ hε → ⊢₁ efq → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ∀ α β → xvar NotFreeIn α → xvar NotFreeIn β → ⊢ dgp α β
hε,efq,tt→rdgp ⊢hε ⊢efq ⊢d0 ⊢¬d1 ⊢d∀ α β x∉α x∉β =
    close
     from∅
     (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ z₅ → z₅ (λ z₆ → z₆) (λ z₆ → z₆ (λ z₇ → z₇ (λ z₈ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ (λ z₁₂ → z₁₂ z₄ (λ z₁₃ → z₁₃ (λ z₁₄ → z₁₄ (λ z₁₅ z₁₆ → z₁₆ (λ z₁₇ → z₁₇) (λ z₁₇ → z₁₇ (λ z₁₈ → z₁₈) z₁₅))) (λ z₁₄ → z₁₄ (λ _ → z₁₀)))) (λ z₁₂ → z₁₂ (λ _ z₁₃ → z₁₃ (λ z₁₄ z₁₅ → z₁₅ z₁₄ z₈)))))) (λ z₇ → z₇ (λ z₈ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ (λ z₁₂ → z₁₂ z₄ (λ z₁₃ → z₁₃ (λ z₁₄ → z₁₄ (λ _ → z₁₀)) (λ z₁₄ → z₁₄ (λ z₁₅ z₁₆ → z₁₆ (λ z₁₇ → z₁₇) (λ z₁₇ → z₁₇ z₁₅ (λ z₁₈ → z₁₈)))))) (λ z₁₂ → z₁₂ (λ z₁₃ z₁₄ → z₁₄ (λ _ z₁₅ → z₁₅ z₁₃ z₈)))))))))))
     (existelim (all⟨ (x∉α ⇒ x∉β) ∨ (x∉β ⇒ x∉α) ⟩ all∪ (all- (all∅ all∪ (all- (all- ((all⟨- β ∷ (D x ∷ [ refl ]) ⟩ all∪ (all- (all∅ all∪ all∅ all∪ all⟨- [ refl ] ⟩)) all∪ (all- all⟨ x∉β ⟩)) all∪ (all- (all- (all⟨- [ refl ] ⟩ all∪ all⟨- (D x ⇒ α) ∷ ((¬D x ⇒ β) ∷ (β ∷ [ refl ])) ⟩)))))) all∪ (all- (all- ((all⟨- α ∷ (¬D x ∷ [ refl ]) ⟩ all∪ (all- all⟨ x∉α ⟩) all∪ (all- (all∅ all∪ all⟨- [ refl ] ⟩ all∪ all∅))) all∪ (all- (all- (all⟨- (D x ⇒ α) ∷ [ refl ] ⟩ all∪ all⟨- (D x ⇒ α) ∷ ((¬D x ⇒ β) ∷ (α ∷ [ refl ])) ⟩)))))))))
      (⊢hε φ)
      (disjelim
       (univelim x (ident (D x ∨ ¬ (D x)) xvar)
        ⊢d∀)
       (disjintro₂ (α ⇒ β)
        (arrowintro β
         (conjelim
          (arrowelim
           (assume (∃x φ ⇒ φ))
           (existintro t1 xvar φ1sub
            (conjintro
             (arrowintro (D t1)
              (arrowelim
               (⊢efq α)
               (arrowelim
                ⊢¬d1
                (assume (D t1)))))
             (arrowintro (¬D t1)
              (assume β)))))
          (arrowelim
           (assume (D x ⇒ α))
           (assume (D x))))))
       (disjintro₁ (β ⇒ α)
        (arrowintro α
         (conjelim
          (arrowelim
           (assume (∃x φ ⇒ φ))
           (existintro t0 xvar φ0sub
            (conjintro
             (arrowintro (D t0) (assume α))
             (arrowintro (¬D t0)
              (arrowelim
               (⊢efq β)
               (arrowelim
                (assume (¬D t0))
                ⊢d0))))))
          (arrowelim
           (assume (¬D x ⇒ β))
           (assume (¬D x))))))))
  where
    φ : Formula
    φ = (D x ⇒ α) ∧ (¬ (D x) ⇒ β)
    φ0sub : φ [ xvar / t0 ]≡ ((D t0 ⇒ α) ∧ (¬ (D t0) ⇒ β))
    φ0sub = (D varterm≡ ⇒ notfree x∉α) ∧ (¬ (D varterm≡) ⇒ notfree x∉β)
    φ1sub : φ [ xvar / t1 ]≡ ((D t1 ⇒ α) ∧ (¬ (D t1) ⇒ β))
    φ1sub = (D varterm≡ ⇒ notfree x∉α) ∧ (¬ (D varterm≡) ⇒ notfree x∉β)

hε,efq,tt→dgp : ⊢₁ hε → ⊢₁ efq → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ⊢₂ dgp
hε,efq,tt→dgp ⊢hε ⊢efq ⊢d0 ⊢¬d1 ⊢d∀ = wlog-dgp (hε,efq,tt→rdgp ⊢hε ⊢efq ⊢d0 ⊢¬d1 ⊢d∀)

Hε,EFQ,TT⊃DGP : Hε ∷ EFQ ∷ TT ⊃ DGP
Hε,EFQ,TT⊃DGP ⊢lhs (α ∷ β ∷ []) =
    hε,efq,tt→dgp
     (descheme₁ (⊢lhs Hε [ refl ]))
     (descheme₁ (⊢lhs EFQ (_ ∷ [ refl ])))
     (descheme₀ (⊢lhs D0 (_ ∷ (_ ∷ [ refl ]))))
     (descheme₀ (⊢lhs ¬D1 (_ ∷ (_ ∷ (_ ∷ [ refl ])))))
     (descheme₀ (⊢lhs D∀ (_ ∷ (_ ∷ (_ ∷ (_ ∷ [ refl ]))))))
     α
     β


wlog-wlem : (∀ α → xvar NotFreeIn α → ⊢ (wlem α)) → ⊢₁ wlem
wlog-wlem ⊢nfwlem α = close
                       from∅
                       (λ x₁ z₁ z₂ → z₂ z₁)
                       (univelim x wlemαω[ω/x]≡wlemα
                        (univintro ωvar all∅
                         (⊢nfwlem αω x∉αω)))
  where
    ω,ωFresh,x≢ω : Σ Variable (λ ω → Σ (ω FreshIn α) (λ _ → xvar ≢ ω))
    ω,ωFresh,x≢ω with fresh (∀x α)
    ω,ωFresh,x≢ω | ω , Λ x≢ω ωFrα = ω , ωFrα , x≢ω
    ωvar          : Variable
    ω∉α           : ωvar NotFreeIn α
    ωFreeForxInα  : (varterm ωvar) FreeFor xvar In α
    x≢ω           : xvar ≢ ωvar
    ωvar          = fst ω,ωFresh,x≢ω
    ω∉α           = freshNotFree (fst (snd ω,ωFresh,x≢ω))
    ωFreeForxInα  = freshFreeFor (fst (snd ω,ωFresh,x≢ω)) xvar
    x≢ω           = snd (snd ω,ωFresh,x≢ω)
    αω        : Formula
    α[x/ω]≡αω : α [ xvar / _ ]≡ αω
    αω        = fst (α [ xvar / ωFreeForxInα ])
    α[x/ω]≡αω = snd (α [ xvar / ωFreeForxInα ])
    wlemαω[ω/x]≡wlemα : (wlem αω) [ ωvar / _ ]≡ (wlem α)
    wlemαω[ω/x]≡wlemα = subInverse
                         ((ω∉α ⇒ atom []) ∨ ((ω∉α ⇒ atom []) ⇒ atom []))
                         ((α[x/ω]≡αω ⇒ notfree (atom []))
                          ∨ ((α[x/ω]≡αω ⇒ notfree (atom []))
                             ⇒ notfree (atom [])))
    x∉αω : xvar NotFreeIn αω
    x∉αω = subNotFree (varterm x≢ω) α[x/ω]≡αω


gmp,tt→rwlem-lemma : ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ∀ α → xvar NotFreeIn α → ⊢ ¬∀x ((D x ⇒ ¬¬ α) ∧ (¬D x ⇒ ¬ α))
gmp,tt→rwlem-lemma ⊢d0 ⊢¬d1 ⊢d∀ α x∉α =
  close
    from∅
    (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅ z₃ (λ z₆ → z₆ (λ _ z₇ → z₇ (λ z₈ z₉ → z₉ z₈ (λ z₁₀ → z₁₀))))) (λ z₅ → z₅ z₃ (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ _ z₉ → z₉ z₇ (λ z₁₀ → z₁₀))))))))
    (arrowintro (∀x φ)
     (arrowelim
      (conjelim
       (univelim t0 φ0sub
        (assume (∀x φ)))
       (arrowelim
        (assume (D t0 ⇒ ¬¬ α))
        ⊢d0))
      (conjelim
       (univelim t1 φ1sub
        (assume (∀x φ)))
       (arrowelim
        (assume (¬D t1 ⇒ ¬ α))
        ⊢¬d1))))
  where
    φ : Formula
    φ = (D x ⇒ ¬¬ α) ∧ (¬D x ⇒ ¬ α)
    φ0sub : φ [ xvar / t0 ]≡ (D t0 ⇒ ¬¬ α) ∧ (¬D t0 ⇒ ¬ α)
    φ0sub = (D varterm≡ ⇒ notfree ((x∉α ⇒ atom []) ⇒ atom [])) ∧ (¬D varterm≡ ⇒ notfree (x∉α ⇒ atom []))
    φ1sub : φ [ xvar / t1 ]≡ (D t1 ⇒ ¬¬ α) ∧ (¬D t1 ⇒ ¬ α)
    φ1sub = (D varterm≡ ⇒ notfree ((x∉α ⇒ atom []) ⇒ atom [])) ∧ (¬D varterm≡ ⇒ notfree (x∉α ⇒ atom []))

gmp,tt→rwlem : ⊢₁ gmp → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ∀ α → xvar NotFreeIn α → ⊢ wlem α
gmp,tt→rwlem ⊢gmp ⊢d0 ⊢¬d1 ⊢d∀ α x∉α =
  close
   from∅
    (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃ (λ z₄ → z₄) (λ z₄ → z₄)) (λ z₃ → z₃ (λ z₄ z₅ → z₅ (λ z₆ → z₆) (λ z₆ → z₆ (λ z₇ → z₇ (λ z₈ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₄ (λ z₁₂ → z₁₂ (λ z₁₃ → z₁₃ (λ _ z₁₄ → z₁₄ (λ z₁₅ z₁₆ → z₁₆ z₁₅ z₁₀))) (λ z₁₃ → z₁₃ (λ z₁₄ z₁₅ → z₁₅ (λ _ z₁₆ → z₁₆ z₁₄ z₈))))))) (λ z₇ → z₇ (λ z₈ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₄ (λ z₁₂ → z₁₂ (λ z₁₃ → z₁₃ (λ z₁₄ z₁₅ → z₁₅ (λ _ z₁₆ → z₁₆ z₈ z₁₄))) (λ z₁₃ → z₁₃ (λ _ → z₁₀)))))))))))
    (existelim (all⟨ (x∉α ⇒ atom []) ∨ ((x∉α ⇒ atom []) ⇒ atom []) ⟩ all∪ (all- (all∅ all∪ (all- (all- (all⟨- α ∷ (D (varterm xvar) ∷ [ refl ]) ⟩ all∪ (all- (all- (all⟨- [ refl ] ⟩ all∪ all⟨ x∉α ⟩))) all∪ (all- (all- (all⟨- α ∷ [ refl ] ⟩ all∪ all⟨- α ∷ (¬D (varterm xvar) ∷ (α ∷ [ refl ])) ⟩)))))) all∪ (all- (all- (all⟨- ¬ α ∷ (¬D (varterm xvar) ∷ [ refl ]) ⟩ all∪ (all- (all- (all⟨- ¬ α ∷ (D (varterm xvar) ∷ (¬ α ∷ [ refl ])) ⟩ all∪ all⟨- ¬ α ∷ [ refl ] ⟩))) all∪ (all- all⟨- ¬D (varterm xvar) ∷ [ refl ] ⟩)))))))
    (arrowelim
     (⊢gmp φ)
     (cite "Lemma" (gmp,tt→rwlem-lemma ⊢d0 ⊢¬d1 ⊢d∀ α x∉α)))
    (disjelim
     (univelim x (ident (D (varterm xvar) ∨ ¬D (varterm xvar)) xvar)
      ⊢d∀)
     (disjintro₁ (¬¬ α)
      (arrowintro α
       (arrowelim
        (assume (¬ φ))
        (conjintro
         (arrowintro (D x)
          (arrowintro (¬ α)
           (arrowelim
            (assume (¬ α))
            (assume α))))
         (arrowintro (¬D x)
          (arrowintro α
           (arrowelim
            (assume (¬D x))
            (assume (D x)))))))))
     (disjintro₂ (¬ α)
      (arrowintro (¬ α)
       (arrowelim
        (assume (¬ φ))
        (conjintro
         (arrowintro (D x)
          (arrowintro (¬ α)
           (arrowelim
            (assume (¬D x))
            (assume (D x)))))
         (arrowintro (¬D x)
          (assume (¬ α)))))))))
  where
    φ : Formula
    φ = (D x ⇒ ¬¬ α) ∧ (¬D x ⇒ ¬ α)
    φ0sub : φ [ xvar / t0 ]≡ (D t0 ⇒ ¬¬ α) ∧ (¬D t0 ⇒ ¬ α)
    φ0sub = (D varterm≡ ⇒ notfree ((x∉α ⇒ atom []) ⇒ atom [])) ∧ (¬D varterm≡ ⇒ notfree (x∉α ⇒ atom []))
    φ1sub : φ [ xvar / t1 ]≡ (D t1 ⇒ ¬¬ α) ∧ (¬D t1 ⇒ ¬ α)
    φ1sub = (D varterm≡ ⇒ notfree ((x∉α ⇒ atom []) ⇒ atom [])) ∧ (¬D varterm≡ ⇒ notfree (x∉α ⇒ atom []))

gmp,tt→wlem : ⊢₁ gmp → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ⊢₁ wlem
gmp,tt→wlem ⊢gmp ⊢d0 ⊢d1 ⊢d∀ = wlog-wlem (gmp,tt→rwlem ⊢gmp ⊢d0 ⊢d1 ⊢d∀)

GMP,TT⊃WLEM : GMP ∷ TT ⊃ WLEM
GMP,TT⊃WLEM ⊢lhs (α ∷ []) =
    gmp,tt→wlem
     (descheme₁ (⊢lhs GMP [ refl ]))
     (descheme₀ (⊢lhs D0 (_ ∷ [ refl ])))
     (descheme₀ (⊢lhs ¬D1 (_ ∷ (_ ∷ [ refl ]))))
     (descheme₀ (⊢lhs D∀ (_ ∷ (_ ∷ (_ ∷ [ refl ])))))
     α

dns∃,tt→rwlem-lemma : ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ∀ α → xvar NotFreeIn α → ⊢ ¬¬∃x ((D x ⇒ ¬¬ α) ∧ (¬D x ⇒ ¬ α))
dns∃,tt→rwlem-lemma ⊢d0 ⊢¬d1 ⊢d∀ α x∉α =
  close
    from∅
    (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ z₃ (λ z₅ → z₅ (λ z₆ → z₆ (λ _ z₇ → z₇ (λ
     z₈ z₉ → z₉ z₃ (λ z₁₀ → z₁₀ (λ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ (λ _ z₁₄ → z₁₄ (λ
     z₁₅ → z₁₅) z₁₂))) (λ z₁₁ → z₁₁ (λ _ → z₈)))))) (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ
     _ z₉ → z₉ z₇ (λ z₁₀ → z₁₀))))))))
    (arrowintro (¬∃x φ)
     (arrowelim
      (assume (¬∃x φ))
      (existintro t0 xvar φ0sub
       (conjintro
        (arrowintro (D t0)
         (arrowintro (¬ α)
          (arrowelim
           (assume (¬∃x φ))
           (existintro t1 xvar φ1sub
            (conjintro
             (arrowintro (D t1)
              (arrowintro (¬ α)
               (arrowelim
                ⊢¬d1
                (assume (D t1)))))
             (arrowintro (¬D t1)
              (assume (¬ α))))))))
        (arrowintro (¬D t0)
         (arrowintro α
          (arrowelim
           (assume (¬D t0))
           ⊢d0)))))))
  where
    φ : Formula
    φ = (D x ⇒ ¬¬ α) ∧ (¬D x ⇒ ¬ α)
    φ0sub : φ [ xvar / t0 ]≡ (D t0 ⇒ ¬¬ α) ∧ (¬D t0 ⇒ ¬ α)
    φ0sub = (D varterm≡ ⇒ notfree ((x∉α ⇒ atom []) ⇒ atom [])) ∧ (¬D varterm≡ ⇒ notfree (x∉α ⇒ atom []))
    φ1sub : φ [ xvar / t1 ]≡ (D t1 ⇒ ¬¬ α) ∧ (¬D t1 ⇒ ¬ α)
    φ1sub = (D varterm≡ ⇒ notfree ((x∉α ⇒ atom []) ⇒ atom [])) ∧ (¬D varterm≡ ⇒ notfree (x∉α ⇒ atom []))

dns∃,tt→rwlem : ⊢₁ dns∃ → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ∀ α → xvar NotFreeIn α → ⊢ wlem α
dns∃,tt→rwlem ⊢dns∃ ⊢d0 ⊢¬d1 ⊢d∀ α x∉α =
  close
   from∅
   (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃ (λ z₄ → z₄) (λ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ (λ z₇ → z₇ (λ z₈ → z₈ (λ _ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₅ (λ z₁₂ → z₁₂ (λ z₁₃ → z₁₃ (λ z₁₄ z₁₅ → z₁₅ (λ _ z₁₆ → z₁₆ (λ z₁₇ → z₁₇) z₁₄))) (λ z₁₃ → z₁₃ (λ _ → z₁₀)))))) (λ z₈ → z₈ (λ z₉ z₁₀ → z₁₀ (λ _ z₁₁ → z₁₁ z₉ (λ z₁₂ → z₁₂)))))))) (λ z₃ → z₃ (λ z₄ z₅ → z₅ (λ z₆ → z₆) (λ z₆ → z₆ (λ z₇ → z₇ (λ z₈ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₄ (λ z₁₂ → z₁₂ (λ z₁₃ z₁₄ → z₁₄ z₁₃ (λ z₁₅ → z₁₅ (λ _ z₁₆ → z₁₆ (λ z₁₇ z₁₈ → z₁₈ (λ z₁₉ → z₁₉ z₁₇ z₈) z₁₀)))))))) (λ z₇ → z₇ (λ z₈ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₄ (λ z₁₂ → z₁₂ (λ z₁₃ z₁₄ → z₁₄ z₁₃ (λ z₁₅ → z₁₅ (λ z₁₆ z₁₇ → z₁₇ (λ _ z₁₈ → z₁₈ (λ z₁₉ → z₁₉ z₁₆ z₈) z₁₀)))))))))))))
   (existelim (all⟨ (x∉α ⇒ atom []) ∨ ((x∉α ⇒ atom []) ⇒ atom []) ⟩ all∪ (all- (all∅ all∪ (all- (all- (all⟨- ¬ α ∷ (D x ∷ [ refl ]) ⟩ all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- (all- ((all⟨- [ refl ] ⟩ all∪ all⟨- (D x ⇒ ¬¬ α) ∷ ((¬D x ⇒ ¬ α) ∷  (((D x ⇒ ¬¬ α) ∧ (¬D x ⇒ ¬ α)) ∷   (¬ α ∷ [ refl ]))) ⟩) all∪ all⟨ x∉α ⇒ atom [] ⟩)))))))) all∪ (all- (all- (all⟨- α ∷ (¬D x ∷ [ refl ]) ⟩ all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- (all- ((all⟨- (D x ⇒ ¬¬ α) ∷ [ refl ] ⟩ all∪ all⟨- (D x ⇒ ¬¬ α) ∷ ((¬D x ⇒ ¬ α) ∷  (((D x ⇒ ¬¬ α) ∧ (¬D x ⇒ ¬ α)) ∷   (α ∷ [ refl ]))) ⟩) all∪ all⟨ x∉α ⟩)))))))))))
    (arrowelim
     (⊢dns∃ φ)
     (arrowintro (¬∃x φ)
      (arrowelim
       (assume (¬∃x φ))
       (existintro t0 xvar φ0sub
        (conjintro
         (arrowintro (D t0)
          (arrowintro (¬ α)
           (arrowelim
            (assume (¬∃x φ))
            (existintro t1 xvar φ1sub
             (conjintro
              (arrowintro (D t1)
               (arrowintro (¬ α)
                (arrowelim
                 ⊢¬d1
                 (assume (D t1)))))
              (arrowintro (¬D t1)
               (assume (¬ α))))))))
         (arrowintro (¬D t0)
          (arrowintro α
           (arrowelim
            (assume (¬D t0))
            ⊢d0))))))))
    (disjelim
     (univelim x (ident (D x ∨ ¬D x) xvar)
      ⊢d∀)
     (disjintro₂ (¬ α)
      (arrowintro (¬ α)
       (arrowelim
        (assume (¬¬ φ))
        (arrowintro φ
         (conjelim
          (assume φ)
          (arrowelim
           (arrowelim
            (assume (D x ⇒ ¬¬ α))
            (assume (D x)))
           (assume (¬ α))))))))
     (disjintro₁ (¬¬ α)
      (arrowintro α
       (arrowelim
        (assume (¬¬ φ))
        (arrowintro φ
         (conjelim
          (assume φ)
          (arrowelim
           (arrowelim
            (assume (¬D x ⇒ ¬ α))
            (assume (¬D x)))
           (assume α)))))))))
  where
    φ : Formula
    φ = (D x ⇒ ¬¬ α) ∧ (¬D x ⇒ ¬ α)
    φ0sub : φ [ xvar / t0 ]≡ (D t0 ⇒ ¬¬ α) ∧ (¬D t0 ⇒ ¬ α)
    φ0sub = (D varterm≡ ⇒ notfree ((x∉α ⇒ atom []) ⇒ atom [])) ∧ (¬D varterm≡ ⇒ notfree (x∉α ⇒ atom []))
    φ1sub : φ [ xvar / t1 ]≡ (D t1 ⇒ ¬¬ α) ∧ (¬D t1 ⇒ ¬ α)
    φ1sub = (D varterm≡ ⇒ notfree ((x∉α ⇒ atom []) ⇒ atom [])) ∧ (¬D varterm≡ ⇒ notfree (x∉α ⇒ atom []))

dns∃,tt→wlem : ⊢₁ dns∃ → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ⊢₁ wlem
dns∃,tt→wlem ⊢dns∃ ⊢d0 ⊢¬d1 ⊢d∀ = wlog-wlem (dns∃,tt→rwlem ⊢dns∃ ⊢d0 ⊢¬d1 ⊢d∀)

DNS∃,TT⊃WLEM : DNS∃ ∷ TT ⊃ WLEM
DNS∃,TT⊃WLEM ⊢lhs (α ∷ []) =
    dns∃,tt→wlem
     (descheme₁ (⊢lhs DNS∃ [ refl ]))
     (descheme₀ (⊢lhs D0 (_ ∷ [ refl ])))
     (descheme₀ (⊢lhs ¬D1 (_ ∷ (_ ∷ [ refl ]))))
     (descheme₀ (⊢lhs D∀ (_ ∷ (_ ∷ (_ ∷ [ refl ])))))
     α

hε,tt→wlem : ⊢₁ hε → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ⊢₁ wlem
hε,tt→wlem ⊢hε ⊢d0 ⊢d1 ⊢d∀ = dns∃,tt→wlem (hε→dns∃ ⊢hε) ⊢d0 ⊢d1 ⊢d∀

dp,tt→wlem : ⊢₁ dp → ⊢₀ d0 → ⊢₀ ¬d1 → ⊢₀ d∀ → ⊢₁ wlem
dp,tt→wlem ⊢dp ⊢d0 ⊢d1 ⊢d∀ = gmp,tt→wlem (dp→gmp ⊢dp) ⊢d0 ⊢d1 ⊢d∀


--------------------------------------------------------------------------------


dp→lpo : ⊢₁ dp → ⊢₂ lpo
dp→lpo ⊢dp α β = close
                  from∅
                  (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ z₃ (λ z₈ → z₈ (λ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₆ z₁₀)) (λ z₉ → z₉ (λ z₁₀ → z₁₀))))))))
                  (arrowintro (∀x (α ∨ β))
                   (existelim
                    (all⟨ Λ↓ xvar α ∨ V↓ xvar β ⟩ all∪ (all- (all⟨ Λ↓ xvar (α ∨ β) ⟩ all∪ (all- (all⟨- α ∷ [ refl ] ⟩ all∪ all⟨- [ refl ] ⟩)) all∪ (all- all⟨- [ refl ] ⟩))))
                    (⊢dp α)
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
DP⊃LPO ⊢lhs (α ∷ β ∷ []) = dp→lpo (descheme₁ (⊢lhs DP [ refl ])) α β



results = join "\n" (""
-- Classical
-- In drinkerexample  ∷ texprop DP   (P x ∷       []) DNE⊃DP
-- In drinkerexample  ∷ texprop Hε   (P x ∷       []) DNE⊃Hε
-- Propositional
  ∷ texprop DNE  (A   ∷       []) LEM,EFQ⊃DNE
  ∷ texprop EFQ  (A   ∷       []) DNE⊃EFQ
  ∷ texprop LEM  (A   ∷       []) DNE⊃LEM
  ∷ texprop WLEM (A   ∷       []) LEM⊃WLEM
  ∷ texprop WLEM (A   ∷       []) DGP⊃WLEM
-- Equivalences
-- In drinker chapter  ∷ texprop GLPO (P x ∷       []) LEM⊃GLPO
-- In drinkerexample   ∷ texprop LEM  (P x ∷       []) GLPO⊃LEM
  ∷ texprop IP   (P x ∷ A   ∷ []) Hε⊃IP
  ∷ texprop Hε   (P x ∷       []) IP⊃Hε
  ∷ texprop WGMP (P x ∷       []) DNS∀⊃WGMP
  ∷ texprop DNS∀ (P x ∷       []) WGMP⊃DNS∀
-- DP and Hε
  ∷ texprop GMP  (P x ∷       []) DP⊃GMP
  ∷ texprop CD   (P x ∷ A   ∷ []) DP⊃CD
  ∷ texprop DNS∃ (P x ∷       []) Hε⊃DNS∃
-- GLPO and GLPO'
  ∷ texprop GMP  (P x ∷       []) GLPO′⊃GMP
-- In drinker chapter  ∷ texprop LEM  (P x ∷       []) GLPO′⊃LEM
  ∷ texprop DNS∃ (P x ∷       []) GLPO⊃DNS∃
-- GMP
  ∷ texprop DNS∃ (P x ∷       []) GMP⊃DNS∃
  ∷ texprop WGMP (P x ∷       []) GMP⊃WGMP
-- Two terms
-- In drinker chapter  ∷ texprop DGP  (P x ∷ Q x ∷ []) DP,EFQ,TT⊃DGP
-- In drinker chapter  ∷ texprop DGP  (P x ∷ Q x ∷ []) Hε,EFQ,TT⊃DGP
-- In drinker chapter  ∷ texprop WLEM (P x ∷       []) DNS∃,TT⊃WLEM
  ∷ [])


dns∀′ dns∃′ : Formula → Formula
dns∀′ Φx = ¬¬∀x Φx ⇒ ∀x¬¬ Φx
dns∃′ Φx = ∃x¬¬ Φx ⇒ ¬¬∃x Φx

⊢dns∀′ : ⊢₁ dns∀′
⊢dns∀′ α = close
            from∅
            (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₃ (λ z₇ → z₇ (λ z₈ z₉ → z₉ z₅ z₈))))))
            (arrowintro (¬¬∀x α)
             (univintro xvar (all- (all⟨ (Λ↓ xvar α ⇒ atom []) ⇒ atom [] ⟩ all∪ (all- (all⟨- ∀x α ∷ [ refl ] ⟩ all∪ all⟨ Λ↓ xvar α ⟩))))
              (arrowintro (¬ α)
               (arrowelim
                (assume (¬¬∀x α))
                (arrowintro (∀x α)
                 (arrowelim
                  (assume (¬ α))
                  (univelim x (ident α xvar)
                   (assume (∀x α)))))))))

⊢dns∀′-prooftree = texdeduction (⊢dns∀′ (P x))

⊢dns∃′ : ⊢₁ dns∃′
⊢dns∃′ α = close
            from∅
            (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ z₃ (λ z₅ → z₅ (λ z₆ z₇ → z₇ (λ z₈ z₉ → z₉ z₆ (λ z₁₀ → z₁₀ (λ z₁₁ z₁₂ → z₁₂ z₈ z₁₁))))))))
            (arrowintro (∃x¬¬ α)
             (existelim (all⟨ (V↓ xvar α ⇒ atom []) ⇒ atom [] ⟩ all∪ (all- (all- (all⟨- ¬∃x α ∷ [ refl ] ⟩ all∪ (all- (all⟨- α ∷ [ refl ] ⟩ all∪ all⟨- [ refl ] ⟩))))))
              (assume (∃x¬¬ α))
              (arrowintro (¬∃x α)
               (arrowelim
                (assume (¬¬ α))
                (arrowintro α
                 (arrowelim
                  (assume (¬∃x α))
                  (existintro (varterm xvar) xvar (ident α xvar)
                  (assume α))))))))

⊢dns∃′-prooftree = texdeduction (⊢dns∃′ (P x))
