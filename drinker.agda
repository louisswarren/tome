open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)
open import Agda.Builtin.Equality
open import Agda.Builtin.String

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


DNE LEM DP GMP : Scheme

dne lem : Formula → Formula
dne α = ¬¬ α ⇒ α
lem α = α ∨ ¬ α

DNE = unaryscheme "DNE" dne
LEM = unaryscheme "LEM" lem


dp gmp : Formula → Formula
dp  Φx = ∃x(Φx ⇒ ∀x Φx)
gmp Φx = ¬∀x Φx ⇒ ∃x (¬ Φx)

DP  = unaryscheme "DP"  dp
GMP = unaryscheme "GMP" gmp

dne→lem : (∀ α → ⊢ (dne α)) → ∀ α → ⊢ (lem α)
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
DNE⊃LEM (⊢dne ∷ []) (α ∷ []) = dne→lem (λ β → ⊢dne (β ∷ [])) α


dp→gmp : (∀ α → ⊢ (dp α)) → ∀ α → ⊢ (gmp α)
dp→gmp ⊢dp α = close
                ((Λ (mkvar zero) α ⇒ atom (mkrel zero zero) []) ~  (∅ ∪   ((α ⇒ Λ (mkvar zero) α) ~ (α ~  (((α ∷ ((α ⇒ Λ (mkvar zero) α) ∷ List.[ refl ])) -∷ ∅) ∪   (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅)))))))
                (arrowintro (¬∀x α)
                 (existelim (V∣ (mkvar zero) (α ⇒ atom (mkrel zero zero) []) ∷  ((α ⇒ Λ (mkvar zero) α) ~   (α ~(((Λ∣ (mkvar zero) α ⇒ atom []) ∷ ∅) ∪ (((α ∷ List.[ refl ]) -∷ ∅) ∪ (List.[ refl ] -∷ ∅))))))
                  (cite "DP" (⊢dp α))
                  (existintro x xvar (ident (α ⇒ atom (mkrel zero zero) []) (varterm (mkvar zero)))
                   (arrowintro α
                    (arrowelim
                     (assume (¬∀x α))
                     (arrowelim
                      (assume (α ⇒ ∀x α))
                      (assume α)))))))
DP⊃GMP : DP ∷ [] ⊃ GMP
DP⊃GMP (⊢dp ∷ []) (α ∷ []) = dp→gmp (λ β → ⊢dp (β ∷ [])) α


s : String
s = texreduce DNE⊃LEM (A ∷ [])
