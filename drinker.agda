open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Agda.Builtin.Sigma

open import Decidable hiding (⊥ ; ¬_)
open import Deduction
open import Ensemble
open import List
open import Formula
open import Scheme
open import Vec

open import Texify

open import sugar


LPO DNE EFQ LEM WLEM DGP GLPO GLPOA GMP WGMP DP HE DNSU DNSE UD IP CD : Scheme


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



dp he : Formula → Formula
dp  Φx = ∃x(Φx ⇒ ∀x Φx)
he  Φx = ∃x(∃x Φx ⇒ Φx)

DP  = unaryscheme dp
HE  = unaryscheme he



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
                           (cite "DNE" (⊢dne α))
                           (arrowintro (¬ α) Γ⊢⊥))

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
                           (cite "EFQ" (⊢efq α))
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
DNE⊃LEM ⊢lhs (α Vec.∷ []) = dne→lem (descheme₁ (⊢lhs DNE [ refl ])) α


dne→efq : ⊢₁ dne → ⊢₁ efq
dne→efq ⊢dne α = close from∅
                  (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ _ → z₃)))))
                  (arrowintro ⊥
                   (arrowelim
                    (cite "DNE" (⊢dne α))
                    (arrowintro (¬ α)
                     (assume ⊥))))
DNE⊃EFQ : DNE ∷ [] ⊃ EFQ
DNE⊃EFQ ⊢lhs (α ∷ []) = dne→efq (descheme₁ (⊢lhs DNE [ refl ])) α

lem,efq→dne : ⊢₁ lem → ⊢₁ efq → ⊢₁ dne
lem,efq→dne ⊢lem ⊢efq α = close from∅
                           (λ x₁ z₁ z₂ → z₂ (z₁  (λ z₃ z₄ →  z₄ (λ z₅ → z₅)  (λ z₅ →     z₅ (λ z₆ → z₆ (λ z₇ → z₇))     (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ z₉ → z₉) (λ z₉ → z₉ z₃ z₇)))))))
                           (arrowintro (¬¬ α)
                            (disjelim
                             (cite "LEM" (⊢lem α))
                             (assume α)
                             (arrowelim
                              (cite "EFQ" (⊢efq α))
                              (arrowelim
                               (assume (¬¬ α))
                               (assume (¬ α))))))
LEM,EFQ⊃DNE : LEM ∷ EFQ ∷ [] ⊃ DNE
LEM,EFQ⊃DNE ⊢lhs (α ∷ []) = lem,efq→dne (descheme₁ (⊢lhs LEM [ refl ])) (descheme₁ (⊢lhs EFQ (_ ∷ [ refl ]))) α


he→ip : ⊢₁ he → ⊢₂ ip
he→ip ⊢he α β = close from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁  (λ z₃ z₄ →  z₄ (λ z₅ → z₅)  (λ z₅ → z₅ (λ z₆ z₇ → z₇ (λ z₈ z₉ → z₉ z₆ (λ z₁₀ → z₁₀ z₃ z₈)))))))
                 (arrowintro (∃x β ⇒ ∃x α)
                  (existelim
                   (all⟨ V∣ xvar (∃x β ⇒ α) ⟩ all∪ (all- (all- (all⟨- ∃x β ∷ [ refl ] ⟩ all∪ all⟨ V∣ xvar β ⇒ V∣ xvar α ⟩ all∪ all⟨ V∣ xvar β ⟩))))
                   (cite "HE" (⊢he α))
                   (existintro x xvar
                    (ident (∃x β ⇒ α) xvar)
                    (arrowintro (∃x β)
                    (arrowelim
                     (assume (∃x α ⇒ α))
                     (arrowelim
                      (assume (∃x β ⇒ ∃x α))
                      (assume (∃x β))))))))
HE⊃IP : HE ∷ [] ⊃ IP
HE⊃IP ⊢lhs (α ∷ β ∷ []) = he→ip (descheme₁ (⊢lhs HE [ refl ])) α β


ip→he : ⊢₂ ip → ⊢₁ he
ip→he ⊢ip α = close from∅
               (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃ (λ z₄ → z₄) (λ z₄ → z₄ (λ z₅ → z₅)))  (λ z₃ → z₃ (λ z₄ → z₄))))
               (existelim
                (all⟨ V∣ xvar (∃x α ⇒ α) ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                (arrowelim
                 (cite "IP" (⊢ip α α))
                 (arrowintro (∃x α)
                  (assume (∃x α))))
                (existintro x xvar
                 (ident (∃x α ⇒ α) xvar)
                 (assume (∃x α ⇒ α))))
IP⊃HE : IP ∷ [] ⊃ HE
IP⊃HE ⊢lhs (α ∷ []) = ip→he (descheme₂ (⊢lhs IP [ refl ])) α


lem→glpo : ⊢₁ lem → ⊢₁ glpo
lem→glpo ⊢lem α = close from∅
                   (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃)  (λ z₃ →  z₃ (λ z₄ → z₄ (λ z₅ → z₅))  (λ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ z₈ → z₈ z₅ z₇))))))
                   (disjelim
                    (cite "LEM" (⊢lem (∃x α)))
                    (disjintro₂ (∀x¬ α)
                     (assume (∃x α)))
                    (disjintro₁ (∃x α)
                     (univintro xvar
                      (all- (all⟨ V∣ xvar α ⇒ atom [] ⟩ all∪ all⟨- [ refl ] ⟩))
                      (arrowintro α
                       (arrowelim
                        (assume (¬∃x α))
                        (existintro x xvar (ident α xvar)
                         (assume α)))))))
LEM⊃GLPO : LEM ∷ [] ⊃ GLPO
LEM⊃GLPO ⊢lhs (α ∷ []) = lem→glpo (descheme₁ (⊢lhs LEM [ refl ])) α


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
                                 (existelim (all⟨ xnfα ⟩ all∪ (all- all⟨ xnfα ⟩))
                                  (assume (∃x α))
                                  (assume α))))
glpo→lem ⊢glpo α | no ¬xnfα = close
                               from∅
                               (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄ (λ z₅ → z₅)) (λ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ (λ z₇ → z₇ (λ z₈ → z₈)))))))
                               (univelim x αω∨¬αω[ω/x]≡α∨¬α
                                (univintro ω (all∅ all∪ (all- all⟨- [ refl ] ⟩) all∪ (all- (all⟨- [ refl ] ⟩ all∪ (all- all⟨- [ refl ] ⟩))))
                                 (disjelim
                                  (cite "GLPO" (⊢glpo αω))
                                  (disjintro₂ αω
                                   (univelim x (ident (¬ αω) xvar)
                                    (assume (∀x (¬ αω)))))
                                  (disjintro₁ (¬ αω)
                                   (existelim (all⟨ xnfαω ⟩ all∪ (all- all⟨- [ refl ] ⟩))
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
                    ωff = freshFreeFor ωFresh xvar
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
GLPO⊃LEM : GLPO ∷ [] ⊃ LEM
GLPO⊃LEM ⊢lhs (α ∷ []) = glpo→lem (descheme₁ (⊢lhs GLPO [ refl ])) α

dnsu→wgmp : ⊢₁ dnsu → ⊢₁ wgmp
dnsu→wgmp ⊢dnsu α = close
                     from∅
                     (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ → z₇ (λ z₈ → z₈) (λ z₈ → z₈ (λ z₉ z₁₀ → z₁₀ z₅ z₉))) z₃))))
                     (arrowintro (¬∀x α)
                      (arrowintro (¬∃x¬ α)
                       (arrowelim
                        (arrowelim
                         (cite "DNS\\forall" (⊢dnsu α))
                         (univintro xvar (all- (all⟨ V∣ xvar (¬ α) ⇒ atom [] ⟩ all∪ all⟨- [ refl ] ⟩))
                          (arrowintro (¬ α)
                           (arrowelim
                            (assume (¬∃x¬ α))
                            (existintro x xvar (ident (¬ α) xvar)
                             (assume (¬ α)))))))
                        (assume (¬∀x α)))))
DNSU⊃WGMP : DNSU ∷ [] ⊃ WGMP
DNSU⊃WGMP ⊢lhs (α ∷ []) = dnsu→wgmp (descheme₁ (⊢lhs DNSU [ refl ])) α

wgmp→dnsu : ⊢₁ wgmp → ⊢₁ dnsu
wgmp→dnsu ⊢wgmp α = close
                     from∅
                     (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ (λ z₇ → z₇ (λ z₈ → z₈) z₅) (λ z₇ → z₇ (λ z₈ z₉ → z₉ z₈ (λ z₁₀ → z₁₀ (λ z₁₁ z₁₂ → z₁₂ z₃ z₁₁))))))))
                     (arrowintro (∀x¬¬ α)
                      (arrowintro (¬∀x α)
                       (arrowelim
                        (arrowelim
                         (cite "WGMP" (⊢wgmp α))
                         (assume (¬∀x α)))
                        (arrowintro (∃x¬ α)
                         (existelim (all⟨ atom [] ⟩ all∪  (all- (all⟨ Λ∣ xvar (¬¬ α) ⟩ all∪ all⟨- [ refl ] ⟩)))
                          (assume (∃x¬ α))
                          (arrowelim
                           (univelim x (ident (¬¬ α) xvar)
                            (assume (∀x¬¬ α)))
                           (assume (¬ α))))))))
WGMP⊃DNSU : WGMP ∷ [] ⊃ DNSU
WGMP⊃DNSU ⊢lhs (α ∷ []) = wgmp→dnsu (descheme₁ (⊢lhs WGMP [ refl ])) α

--dp→dp′ : ⊢₁ dp → ∀ α ωvar → (ff : (varterm ωvar) FreeFor xvar In α) → ⊢ V ωvar (Λ xvar (fst (α [ xvar / ff ]) ⇒ α))
--dp→dp′ ⊢dp α ωvar ωffx = close {!   !} {!   !} (existelim {!   !} (cite "DP" (⊢dp α)) (existintro {!   !} {!   !} {!   !} {!   !}))

dne→dp : ⊢₁ dne → ⊢₁ dp
dne→dp ⊢dne α = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄ (λ z₆ → z₆ (λ _ z₇ → z₇ (λ z₈ → z₈) (λ z₈ → z₈ (λ z₉ z₁₀ → z₁₀ z₄ (λ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ (λ z₁₄ → z₁₄) (λ z₁₄ → z₁₄ (λ _ z₁₅ → z₁₅ z₉ z₁₂))))))))))))
                 (arrowelim
                  (cite "DNE" (⊢dne (dp α)))
                  (arrowintro (¬ (dp α))
                   (arrowelim
                    (assume (¬ (dp α)))
                    (existintro x xvar (ident (α ⇒ ∀x α) xvar)
                     (arrowintro α
                      (univintro xvar (all∅ all∪ (all- (all⟨ V∣ xvar (α ⇒ ∀x α) ⇒ atom [] ⟩ all∪ (all- (all∅ all∪ (all- (all⟨- ¬∀x α ∷ (α ∷ [ refl ]) ⟩ all∪ all⟨- ¬∀x α ∷ [ refl ] ⟩)))))))
                       (arrowelim
                        (cite "DNE" (⊢dne α))
                        (arrowintro (¬ α)
                         (arrowelim
                          (assume (¬ (dp α)))
                          (existintro x xvar (ident (α ⇒ ∀x α) xvar)
                          (arrowintro α
                           (arrowelim
                            (cite "DNE" (⊢dne (∀x α)))
                            (arrowintro (¬∀x α)
                             (arrowelim
                              (assume (¬ α))
                              (assume α)))))))))))))))
DNE⊃DP : DNE ∷ [] ⊃ DP
DNE⊃DP ⊢lhs (α ∷ []) = dne→dp (descheme₁ (⊢lhs DNE [ refl ])) α

s = texreduce DNE⊃DP (P x ∷ [])

--------------------------------------------------------------------------------
dp→gmp : ⊢₁ dp → ⊢₁ gmp
dp→gmp ⊢dp α = close
                from∅
                (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ (λ z₈ z₉ → z₉ z₃ (λ z₁₀ → z₁₀ z₆ z₈)))))))
                (arrowintro (¬∀x α)
                 (existelim (all⟨ V∣ xvar (¬ α) ⟩ all∪ (all- (all- (all⟨ Λ∣ xvar α ⇒ atom [] ⟩ all∪ all⟨- α ∷ [ refl ] ⟩ all∪ all⟨- [ refl ] ⟩))))
                  (cite "DP" (⊢dp α))
                  (existintro x xvar (ident (¬ α) xvar)
                   (arrowintro α
                    (arrowelim
                     (assume (¬∀x α))
                     (arrowelim
                      (assume (α ⇒ ∀x α))
                      (assume α)))))))
DP⊃GMP : DP ∷ [] ⊃ GMP
DP⊃GMP ⊢lhs (α ∷ []) = dp→gmp (descheme₁ (⊢lhs DP [ refl ])) α


dp→lpo : ⊢₁ dp → ⊢₂ lpo
dp→lpo ⊢dp α β = close
                  from∅
                  (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ z₃ (λ z₈ → z₈ (λ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₆ z₁₀)) (λ z₉ → z₉ (λ z₁₀ → z₁₀))))))))
                  (arrowintro (∀x (α ∨ β))
                   (existelim
                    (all⟨ Λ∣ xvar α ∨ V∣ xvar β ⟩ all∪ (all- (all⟨ Λ∣ xvar (α ∨ β) ⟩ all∪ (all- (all⟨- α ∷ [ refl ] ⟩ all∪ all⟨- [ refl ] ⟩)) all∪ (all- all⟨- [ refl ] ⟩))))
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
DP⊃LPO ⊢lhs (α ∷ β ∷ []) = dp→lpo (descheme₁ (⊢lhs DP [ refl ])) α β


dp→cd : ⊢₁ dp → ⊢₂ cd
dp→cd ⊢dp α β = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ → z₅) (λ z₅ → z₅ (λ z₆ z₇ → z₇ z₃ (λ z₈ → z₈ (λ z₉ → z₉ (λ z₁₀ z₁₁ → z₁₁ z₆ z₁₀)) (λ z₉ → z₉ (λ z₁₀ → z₁₀))))))))
                 (arrowintro (∀x (α ∨ ∃x β))
                  (existelim (all⟨ Λ∣ xvar α ∨ V∣ xvar β ⟩ all∪ (all- (all⟨ Λ∣ xvar (α ∨ ∃x β) ⟩ all∪ (all- (all⟨- α ∷ [ refl ] ⟩ all∪ all⟨- [ refl ] ⟩)) all∪ (all- all⟨ V∣ xvar β ⟩))))
                   (cite "DP" (⊢dp α))
                   (disjelim
                    (univelim x (ident (α ∨ ∃x β) xvar)
                     (assume (∀x (α ∨ ∃x β))))
                    (disjintro₁ (∃x β) (arrowelim (assume (α ⇒ ∀x α)) (assume α)))
                    (disjintro₂ (∀x α) (assume (∃x β))))))
DP⊃CD : DP ∷ [] ⊃ CD
DP⊃CD ⊢lhs (α ∷ β ∷ []) = dp→cd (descheme₁ (⊢lhs DP [ refl ])) α β
