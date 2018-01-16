module common where

open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.List
open import Agda.Builtin.String

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

