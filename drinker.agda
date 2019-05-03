open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Sigma

open import Decidable hiding (⊥ ; ¬_)
open import Deduction
open import Menge
open import List
  hiding (Any ; any)
  renaming (
    All        to All[]        ;
    all        to all[]        ;
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    decide∈    to decide[∈]    )
open import Formula
open import Scheme
open import Vec

open import Texify

open import sugar


LPO DNE EFQ LEM WLEM DGP GLPO GLPOA GMP WGMP DP HE DPN HEN DNSU DNSE UD IP CD : Scheme


lpo : Formula → Formula → Formula
lpo Φx Ψx = ∀x (Φx ∨ Ψx) ⇒ ∀x Φx ∨ ∃x Ψx

LPO = binaryscheme lpo

dne : Formula → Formula
dne Φ = ¬¬ Φ ⇒ Φ

DNE = unaryscheme dne

efq : Formula → Formula
efq Φ = ⊥ ⇒ Φ

EFQ = unaryscheme efq


lem wlem : Formula → Formula
lem  Φ = Φ ∨ ¬ Φ
wlem Φ = ¬ Φ ∨ ¬¬ Φ

LEM  = unaryscheme lem
WLEM = unaryscheme wlem



dgp : Formula → Formula → Formula
dgp Φ Ψ  = (Φ ⇒ Ψ) ∨ (Ψ ⇒ Φ)

DGP = binaryscheme dgp



glpo glpoa gmp wgmp : Formula → Formula
glpo  Φx = ∀x ¬Φx ∨ ∃x Φx                                       where ¬Φx = ¬ Φx
glpoa Φx = ∀x Φx ∨ ∃x ¬Φx                                       where ¬Φx = ¬ Φx
gmp   Φx = ¬∀x Φx ⇒ ∃x ¬Φx                                      where ¬Φx = ¬ Φx
wgmp  Φx = ¬∀x Φx ⇒ ¬¬(∃x ¬Φx)                                  where ¬Φx = ¬ Φx

GLPO  = unaryscheme glpo
GLPOA = unaryscheme glpoa
GMP   = unaryscheme gmp
WGMP  = unaryscheme wgmp



dp he dpn hen : Formula → Formula
dp  Φx = ∃x(Φx ⇒ ∀x Φx)
he  Φx = ∃x(∃x Φx ⇒ Φx)
dpn Φx = dp (¬ Φx)
hen Φx = he (¬ Φx)

DP  = unaryscheme dp
HE  = unaryscheme he
DPN = unaryscheme dpn
HEN = unaryscheme hen



dnsu dnse : Formula → Formula
dnsu Φx = ∀x(¬¬ Φx) ⇒ ¬¬(∀x Φx)
dnse Φx = ¬¬(∃x Φx) ⇒ ∃x (¬¬ Φx)

DNSU = unaryscheme dnsu
DNSE = unaryscheme dnse

cd : Formula → Formula → Formula
cd Φx Ψ = ∀x (Φx ∨ ∃x Ψ) ⇒ ∀x Φx ∨ ∃x Ψ

CD = binaryscheme cd


-- These are usually stated with Ψ instead of ∃x Ψ, but this is a simple way of
-- adding bounded variable requirements as x is certainly not free in ∃x Ψ.
-- If x is in fact not free in Ψ, then the existential can be eliminated
-- separately.
ud ip : Formula → Formula → Formula
ud Φx Ψ = ∀x (Φx ∨ (∃x Ψ)) ⇒ (∀x Φx ∨ ∃x Ψ)
ip Φx Ψ = (∃x Ψ ⇒ ∃x Φx) ⇒ ∃x(∃x Ψ ⇒ Φx)

UD = binaryscheme ud
IP = binaryscheme ip







dne→lem : ⊢₁ dne → ⊢₁ lem
dne→lem ⊢dne α = close from∅
                  (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃)  (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄ (λ z₆ → z₆ (λ z₇ z₈ → z₈ z₄ z₇))))))
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
DNE⊃LEM : DNE List.∷ [] ⊃ LEM
DNE⊃LEM x₁ (α Vec.∷ []) = dne→lem (descheme₁ (x₁ DNE [ refl ])) α

k = texreduce DNE⊃LEM (A Vec.∷ [])


dne→efq : ⊢₁ dne → ⊢₁ efq
dne→efq ⊢dne α = close from∅
                  (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ _ → z₃)))))
                  (arrowintro ⊥ (arrowelim (cite "DNE" (⊢dne α)) (arrowintro (¬ α) (assume ⊥))))

lem,efq→dne : ⊢₁ lem → ⊢₁ efq → ⊢₁ dne
lem,efq→dne ⊢lem ⊢efq α = close from∅
                           (λ x₁ z₁ z₂ → z₂ (z₁  (λ z₃ z₄ →  z₄ (λ z₅ → z₅)  (λ z₅ →     z₅ (λ z₆ → z₆ (λ z₇ → z₇))     (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ z₉ → z₉) (λ z₉ → z₉ z₃ z₇)))))))
                           (arrowintro (¬¬ α) (disjelim (cite "LEM" (⊢lem α)) (assume α) (arrowelim (cite "EFQ" (⊢efq α)) (arrowelim (assume (¬¬ α)) (assume (¬ α))))))


ttttt : ∀ α → Menge.All (λ k → (xvar NotFreeIn k)) (⟨ ∃x α ⟩)
ttttt α = all⟨ V∣ xvar α ⟩

he→ip : ⊢₁ he → ⊢₂ ip
he→ip ⊢he α β = close from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁  (λ z₃ z₄ →  z₄ (λ z₅ → z₅)  (λ z₅ → z₅ (λ z₆ z₇ → z₇ (λ z₈ z₉ → z₉ z₆ (λ z₁₀ → z₁₀ z₃ z₈)))))))
                 (arrowintro (∃x β ⇒ ∃x α)
                  (existelim
                   (all⟨ V∣ xvar (∃x β ⇒ α) ⟩ all∪  ((∃x α ⇒ α) all~   (∃x β all~ (all-⟨ ∃x β ∷ [ refl ] ⟩ all∪  (all⟨ V∣ xvar β ⇒ V∣ xvar α ⟩ all∪ all⟨ V∣ xvar β ⟩)))))
                   (cite "HE" (⊢he α))
                   (existintro x xvar
                    (ident (∃x β ⇒ α) xvar)
                    (arrowintro (∃x β)
                    (arrowelim
                     (assume (∃x α ⇒ α))
                     (arrowelim
                      (assume (∃x β ⇒ ∃x α))
                      (assume (∃x β))))))))


ip→he : ⊢₂ ip → ⊢₁ he
ip→he ⊢ip α = close from∅
               (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃ (λ z₄ → z₄) (λ z₄ → z₄ (λ z₅ → z₅)))  (λ z₃ → z₃ (λ z₄ → z₄))))
               (existelim
                (all⟨ V∣ xvar (∃x α ⇒ α) ⟩ all∪ ((∃x α ⇒ α) all~ all-⟨ [ refl ] ⟩))
                (arrowelim
                 (cite "IP" (⊢ip α α))
                 (arrowintro (∃x α)
                  (assume (∃x α))))
                (existintro x xvar
                 (ident (∃x α ⇒ α) xvar)
                 (assume (∃x α ⇒ α))))


lem→glpo : ⊢₁ lem → ⊢₁ glpo
lem→glpo ⊢lem α = close from∅
                   (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃)  (λ z₃ →  z₃ (λ z₄ → z₄ (λ z₅ → z₅))  (λ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ z₈ → z₈ z₅ z₇))))))
                   (disjelim
                    (cite "LEM" (⊢lem (∃x α)))
                    (disjintro₂ (∀x¬ α)
                     (assume (∃x α)))
                    (disjintro₁ (∃x α)
                     (univintro xvar
                      (α all~ (all⟨ V∣ xvar α ⇒ atom [] ⟩ all∪ all-⟨ [ refl ] ⟩))
                      (arrowintro α
                       (arrowelim
                        (assume (¬∃x α))
                        (existintro x xvar (ident α xvar)
                         (assume α)))))))

glpo→lem : ⊢₁ glpo → ⊢₁ lem
glpo→lem ⊢glpo α with xvar notFreeIn α
glpo→lem ⊢glpo α | yes xnfα = close
                               from∅
                               (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄ (λ z₅ → z₅)) (λ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ (λ z₇ → z₇ (λ z₈ → z₈)))))))
                               (disjelim
                                (cite "GLPO" (⊢glpo α))
                                (disjintro₂ α
                                 (univelim x (ident (¬ α) xvar)
                                  (assume (∀x¬ α))))
                                (disjintro₁ (¬ α)
                                 (existelim (all⟨ xnfα ⟩ all∪ (α all~ all⟨ xnfα ⟩))
                                  (assume (∃x α))
                                  (assume α))))
glpo→lem ⊢glpo α | no ¬xnfα = close
                               from∅
                               (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄ (λ z₅ → z₅)) (λ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ (λ z₇ → z₇ (λ z₈ → z₈)))))))
                               (univelim x αω∨¬αω[ω/x]≡α∨¬α
                                (univintro ω (all∅ all∪ (∀x (¬ αω) all~ all-⟨ [ refl ] ⟩) all∪ (∃x αω all~ (all-⟨ [ refl ] ⟩ all∪ (αω all~ all-⟨ [ refl ] ⟩))))
                                 (disjelim
                                  (cite "GLPO" (⊢glpo αω))
                                  (disjintro₂ αω
                                   (univelim x (ident (¬ αω) xvar)
                                    (assume (∀x (¬ αω)))))
                                  (disjintro₁ (¬ αω)
                                   (existelim (all⟨ xnfαω ⟩ all∪ (αω all~ all-⟨ [ refl ] ⟩))
                                    (assume (∃x αω))
                                    (assume αω))))))
                   where
                    ω : Variable
                    ω = fst (fresh α)
                    ωFresh : ω FreshIn α
                    ωFresh = snd (fresh α)
                    ωnf : ω NotFreeIn α
                    ωnf = freshNotFree ωFresh
                    ωff : (varterm ω) FreeFor xvar In α
                    ωff = freshFreeFor ωFresh
                    αω : Formula
                    αω = fst (α [ xvar / ωff ])
                    αωpf : α [ xvar / varterm ω ]≡ αω
                    αωpf = snd (α [ xvar / ωff ])
                    ≡ωnf : ∀ x → x ≡ ω → x NotFreeIn α
                    ≡ωnf x refl = ωnf
                    xnfαω : xvar NotFreeIn αω
                    xnfαω with varEq xvar ω
                    xnfαω | yes x≡ω = ⊥-elim (¬xnfα (≡ωnf xvar x≡ω))
                    xnfαω | no  x≢ω = subNotFree (varterm x≢ω) αωpf
                    αω[ω/x]≡α : αω [ ω / x ]≡ α
                    αω[ω/x]≡α = subInverse ωnf αωpf
                    αω∨¬αω[ω/x]≡α∨¬α : (αω ∨ ¬ αω)[ ω / x ]≡ (α ∨ ¬ α)
                    αω∨¬αω[ω/x]≡α∨¬α = αω[ω/x]≡α ∨ (αω[ω/x]≡α ⇒ notfree (atom []))


dp→gmp : ⊢₁ dp → ⊢₁ gmp
dp→gmp ⊢dp α = close
                from∅
                (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ (λ z₈ z₉ → z₉ z₃ (λ z₁₀ → z₁₀ z₆ z₈)))))))
                (arrowintro (¬∀x α)
                 (existelim (all⟨ V∣ xvar (¬ α) ⟩ all∪ (α ⇒ ∀x α all~ (α all~ (all⟨ Λ∣ xvar α ⇒ atom [] ⟩ all∪ all-⟨ α ∷ [ refl ] ⟩ all∪ all-⟨ [ refl ] ⟩))))
                  (cite "DP" (⊢dp α))
                  (existintro x xvar (ident (¬ α) xvar)
                   (arrowintro α
                    (arrowelim
                     (assume (¬∀x α))
                     (arrowelim
                      (assume (α ⇒ ∀x α))
                      (assume α)))))))


dp→lpo : ⊢₁ dp → ⊢₂ lpo
dp→lpo ⊢dp α β = close
                  from∅
                  (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ z₃ (λ z₈ → z₈ (λ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₆ z₁₀)) (λ z₉ → z₉ (λ z₁₀ → z₁₀))))))))
                  (arrowintro (∀x (α ∨ β))
                   (existelim
                    (all⟨ Λ∣ xvar α ∨ V∣ xvar β ⟩ all∪ (α ⇒ ∀x α all~ (all⟨ Λ∣ xvar (α ∨ β) ⟩ all∪ (α all~ (all-⟨ α ∷ [ refl ] ⟩ all∪ all-⟨ [ refl ] ⟩)) all∪ (β all~ all-⟨ [ refl ] ⟩))))
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


dp→cd : ⊢₁ dp → ⊢₂ cd
dp→cd ⊢dp α β = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ z₃ (λ z₈ → z₈ (λ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₆ z₁₀)) (λ z₉ → z₉ (λ z₁₀ → z₁₀))))))))
                 (arrowintro (∀x (α ∨ ∃x β))
                  (existelim (all⟨ Λ∣ xvar α ∨ V∣ xvar β ⟩ all∪ (α ⇒ ∀x α all~ (all⟨ Λ∣ xvar (α ∨ ∃x β) ⟩ all∪ (α all~ (all-⟨ α ∷ [ refl ] ⟩ all∪ all-⟨ [ refl ] ⟩)) all∪ (∃x β all~ all⟨ V∣ xvar β ⟩))))
                   (cite "DP" (⊢dp α))
                   (disjelim
                    (univelim x (ident (α ∨ ∃x β) xvar)
                     (assume (∀x (α ∨ ∃x β))))
                    (disjintro₁ (∃x β) (arrowelim (assume (α ⇒ ∀x α)) (assume α)))
                    (disjintro₂ (∀x α) (assume (∃x β))))))

