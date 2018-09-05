module Decidable where

open import Agda.Builtin.Equality public

data ⊥ : Set where

¬_ : (A : Set) → Set
¬ A = A → ⊥

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬(x ≡ y)

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

Pred : Set → Set₁
Pred A = A → Set

Decidable : {A : Set} → Pred A → Set
Decidable P = ∀ x → Dec (P x)

Decidable≡ : Set → Set
Decidable≡ A = (x y : A) → Dec (x ≡ y)
