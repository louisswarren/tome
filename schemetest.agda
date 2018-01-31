open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Formula
open import Deduction
open import Scheme
open import common

Q = propatom (mkprop "Q")


lemf : Vec Formula 1 → Formula
lemf (x ∷ []) = x ∨ ¬ x
lem : (1)-aryScheme
lem = record { name = "LEM"; func = lemf }

dgpf : Vec Formula 2 → Formula
dgpf (x ∷ y ∷ []) = (x ⇒ y) ∨ (y ⇒ x)

dgp : (2)-aryScheme
dgp = record { name = "DGP"; func = dgpf }


data Abslist {A : Set}(IA : A → Set) : Set where
  []  : Abslist IA


Ax : ∀{n k} → (n)-aryScheme → Vec ΣScheme k → Vec ΣScheme (suc k)
Ax {n} x xs = (n ↦ x) ∷ xs


pf : Ax dgp (Ax lem []) , [] ⊢ Q ∨ ¬ Q
pf = axiom 1 (Q ∷ [])

