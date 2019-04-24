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

--open import Texify

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
dne→lem ⊢dne α = close
                  ? -- (∅ ∪ ((α ∨ (α ⇒ atom (rel zero zero) []) ⇒ atom (rel zero zero) [])   ~   ((List.[ refl ] -∷ ∅) ∪ (α ~ (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅))))))
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


dne→efq : ⊢₁ dne → ⊢₁ efq
dne→efq ⊢dne α = close
                  (λ x₁ z₁ → z₁ (λ z₂ → ⊥-elim (z₂ (λ z₃ → z₃) (λ z₃ → ⊥-elim (z₃ (λ z₄ → z₁ (λ _ → z₄)))))))
--                  (λ { δ (⊥≢δ , inl δ∈∅)               → δ∈∅
--                     ; δ (⊥≢δ , inr (α⇒⊥≢δ , inl ⊥≡δ)) → ⊥≢δ ⊥≡δ
--                     ; δ (⊥≢δ , inr (α⇒⊥≢δ , inr δ∈∅)) → δ∈∅     })
                  (arrowintro ⊥ (arrowelim (cite "DNE" (⊢dne α)) (arrowintro (¬ α) (assume ⊥))))

lem,efq→dne : ⊢₁ lem → ⊢₁ efq → ⊢₁ dne
lem,efq→dne ⊢lem ⊢efq α = close
                           {! ⊥-elim -t 60  !}
                           -- (¬¬ α ~ ∅ ∪ (α ~ [ refl ] -∷ ∅) ∪ ¬ α ~ ∅ ∪ ((¬ α ∷ [ refl ]) -∷ ∅) ∪ [ refl ] -∷ ∅)
                           (arrowintro (¬¬ α) (disjelim (cite "LEM" (⊢lem α)) (assume α) (arrowelim (cite "EFQ" (⊢efq α)) (arrowelim (assume (¬¬ α)) (assume (¬ α))))))


--he→ip : ⊢₁ he → ⊢₂ ip
--he→ip ⊢he α β = close
--                 ? -- ((∃x β ⇒ ∃x α) ~ (∅ ∪ ((∃x α ⇒ α) ~(∃x β ~ (((∃x β ∷ [ refl ]) -∷ ∅) ∪ (((∃x β ∷ ((∃x α ⇒ α) ∷ [ refl ])) -∷ ∅) ∪ ([ refl ] -∷ ∅)))))))
--                 (arrowintro (∃x β ⇒ ∃x α) (existelim (V∣ xvar (∃x β ⇒ α) ∷ ((∃x α ⇒ α) ~ (∃x β ~(((∃x β ∷ [ refl ]) -∷ ∅) ∪ (((V∣ xvar β ⇒ V∣ xvar α) ∷ ∅) ∪ (V∣ xvar β ∷ ∅)))))) (cite "HE" (⊢he α)) (existintro x xvar (ident (∃x β ⇒ α) xvar) (arrowintro (∃x β) (arrowelim (assume (∃x α ⇒ α)) (arrowelim (assume (∃x β ⇒ ∃x α)) (assume (∃x β))))))))
--
--
--ip→he : ⊢₂ ip → ⊢₁ he
--ip→he ⊢ip α = close ((∅ ∪ (∃x α ~ ([ refl ] -∷ ∅))) ∪ ((∃x α ⇒ α) ~ ([ refl ] -∷ ∅))) (existelim (V∣ xvar (∃x α ⇒ α) ∷ ((∃x α ⇒ α) ~ ([ refl ] -∷ ∅))) (arrowelim (cite "IP" (⊢ip α α)) (arrowintro (∃x α) (assume (∃x α)))) (existintro x xvar (ident (∃x α ⇒ α) xvar) (assume (∃x α ⇒ α))))
--
--
--lem→glpo : ⊢₁ lem → ⊢₁ glpo
--lem→glpo ⊢lem α = close
--                   (∅ ∪ (∃x α ~ [ refl ] -∷ ∅) ∪ ¬∃x α ~ α ~ ((α ∷ [ refl ]) -∷ ∅) ∪ [ refl ] -∷ ∅)
--                   (disjelim
--                    (cite "LEM" (⊢lem (∃x α)))
--                    (disjintro₂ (∀x¬ α)
--                     (assume (∃x α)))
--                    (disjintro₁ (∃x α)
--                     (univintro xvar (α ~ (((V∣ xvar α ⇒ atom []) ∷ ∅) ∪ ([ refl ] -∷ ∅)))
--                      (arrowintro α
--                       (arrowelim
--                        (assume (¬∃x α))
--                        (existintro x xvar (ident α xvar)
--                         (assume α)))))))
--
--glpo→lem : ⊢₁ glpo → ⊢₁ lem
--glpo→lem ⊢glpo α with xvar notFreeIn α
--glpo→lem ⊢glpo α | yes xnfα = close
--                               (∅ ∪  (∀x¬ α ~ [ refl ] -∷ ∅) ∪  ∃x α ~ ([ refl ] -∷ ∅) ∪ α ~ [ refl ] -∷ ∅)
--                               (disjelim
--                                (cite "GLPO" (⊢glpo α))
--                                (disjintro₂ α
--                                 (univelim x (ident (¬ α) xvar)
--                                  (assume (∀x¬ α))))
--                                (disjintro₁ (¬ α)
--                                 (existelim (xnfα ∷ α ~ [ refl ] -∷ ∅)
--                                  (assume (∃x α))
--                                  (assume α))))
--glpo→lem ⊢glpo α | no ¬xnfα = close
--                               (∅ ∪ (∀x¬ αω ~ [ refl ] -∷ ∅) ∪ (∃x αω ~ (([ refl ] -∷ ∅) ∪ (αω ~ [ refl ] -∷ ∅))))
--                               (univelim x αω∨¬αω[ω/x]≡α∨¬α
--                                (univintro ω (∅ ∪ (∀x¬ αω ~ [ refl ] -∷ ∅) ∪ (∃x αω ~ (([ refl ] -∷ ∅) ∪ (αω ~ [ refl ] -∷ ∅))))
--                                 (disjelim
--                                  (cite "GLPO" (⊢glpo αω))
--                                  (disjintro₂ αω
--                                   (univelim x (ident (¬ αω) xvar)
--                                    (assume (∀x (¬ αω)))))
--                                  (disjintro₁ (¬ αω)
--                                   (existelim (xnfαω ∷ αω ~ [ refl ] -∷ ∅)
--                                    (assume (∃x αω))
--                                    (assume αω))))))
--                   where
--                    ω : Variable
--                    ω = fst (fresh α)
--                    ωFresh : ω FreshIn α
--                    ωFresh = snd (fresh α)
--                    ωnf : ω NotFreeIn α
--                    ωnf = freshNotFree ωFresh
--                    ωff : (varterm ω) FreeFor xvar In α
--                    ωff = freshFreeFor ωFresh
--                    αω : Formula
--                    αω = fst (α [ xvar / ωff ])
--                    αωpf : α [ xvar / varterm ω ]≡ αω
--                    αωpf = snd (α [ xvar / ωff ])
--                    ≡ωnf : ∀ x → x ≡ ω → x NotFreeIn α
--                    ≡ωnf x refl = ωnf
--                    xnfαω : xvar NotFreeIn αω
--                    xnfαω with varEq xvar ω
--                    xnfαω | yes x≡ω = ⊥-elim (¬xnfα (≡ωnf xvar x≡ω))
--                    xnfαω | no  x≢ω = subNotFree (varterm x≢ω) αωpf
--                    αω[ω/x]≡α : αω [ ω / x ]≡ α
--                    αω[ω/x]≡α = subInverse ωnf αωpf
--                    αω∨¬αω[ω/x]≡α∨¬α : (αω ∨ ¬ αω)[ ω / x ]≡ (α ∨ ¬ α)
--                    αω∨¬αω[ω/x]≡α∨¬α = αω[ω/x]≡α ∨ (αω[ω/x]≡α ⇒ notfree (atom []))
--
--
--dp→gmp : ⊢₁ dp → ⊢₁ gmp
--dp→gmp ⊢dp α = close
--                ((Λ (var zero) α ⇒ atom (rel zero zero) []) ~ (∅ ∪ ((α ⇒ Λ (var zero) α) ~ (α ~ (((α ∷ ((α ⇒ Λ (var zero) α) ∷ List.[ refl ])) -∷ ∅) ∪ (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅)))))))
--                (arrowintro (¬∀x α)
--                 (existelim (V∣ (var zero) (α ⇒ atom (rel zero zero) []) ∷ ((α ⇒ Λ (var zero) α) ~ (α ~(((Λ∣ (var zero) α ⇒ atom []) ∷ ∅) ∪ (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅))))))
--                  (cite "DP" (⊢dp α))
--                  (existintro x xvar (ident (¬ α) xvar)
--                   (arrowintro α
--                    (arrowelim
--                     (assume (¬∀x α))
--                     (arrowelim
--                      (assume (α ⇒ ∀x α))
--                      (assume α)))))))
--
--
--dp→lpo : ⊢₁ dp → ⊢₂ lpo
--dp→lpo ⊢dp α β = close
--                  (∀x (α ∨ β) ~ ∅ ∪ α ⇒ ∀x α ~ (((α ⇒ ∀x α) ∷ [ refl ]) -∷ ∅) ∪ (α ~ ((α ∷ [ refl ]) -∷ ∅) ∪ [ refl ] -∷ ∅) ∪ β ~ [ refl ] -∷ ∅)
--                  (arrowintro (∀x (α ∨ β))
--                   (existelim
--                    (Λ∣ xvar α ∨ V∣ xvar β ∷ α ⇒ ∀x α ~ (Λ∣ xvar (α ∨ β) ∷ ∅) ∪ (α ~ ((α ∷ [ refl ]) -∷ ∅) ∪ [ refl ] -∷ ∅) ∪ β ~ [ refl ] -∷ ∅)
--                    (cite "DP" (⊢dp α))
--                    (disjelim
--                     (univelim x (ident (α ∨ β) xvar)
--                      (assume (∀x (α ∨ β))))
--                     (disjintro₁ (∃x β)
--                      (arrowelim
--                       (assume (α ⇒ ∀x α))
--                       (assume α)))
--                     (disjintro₂ (∀x α)
--                      (existintro x xvar (ident β xvar)
--                       (assume β))))))
--
--
--dp→cd : ⊢₁ dp → ⊢₂ cd
--dp→cd ⊢dp α β = close
--                 (∀x (α ∨ ∃x β) ~ (∅ ∪ (α ⇒ ∀x α ~ ((((α ⇒ ∀x α) ∷ [ refl ]) -∷ ∅) ∪ (α ~ (((α ∷ [ refl ]) -∷ ∅) ∪ ([ refl ] -∷ ∅))) ∪ (∃x β ~ [ refl ] -∷ ∅)))))
--                 (arrowintro (∀x (α ∨ ∃x β))
--                  (existelim (Λ∣ xvar α ∨ V∣ xvar β ∷ α ⇒ ∀x α ~ ((Λ∣ xvar (α ∨ ∃x β) ∷ ∅) ∪ (α ~ (((α ∷ [ refl ]) -∷ ∅) ∪ ([ refl ] -∷ ∅))) ∪ (∃x β ~ V∣ xvar β ∷ ∅)))
--                   (cite "DP" (⊢dp α))
--                   (disjelim
--                    (univelim x (ident (α ∨ ∃x β) xvar)
--                     (assume (∀x (α ∨ ∃x β))))
--                    (disjintro₁ (∃x β) (arrowelim (assume (α ⇒ ∀x α)) (assume α)))
--                    (disjintro₂ (∀x α) (assume (∃x β))))))
--
