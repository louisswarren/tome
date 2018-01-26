module common where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

maxℕ : ℕ → ℕ → ℕ
maxℕ zero    m       = m
maxℕ n       zero    = n
maxℕ (suc n) (suc m) = suc (maxℕ n m)


max : {A : Set} → A → (A → A → A) → List A → A
max d f [] = d
max d f (x ∷ xs) = f x (max d f xs)


map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs


record Σ (I : Set)(I→S : I → Set) : Set where
  constructor _,_
  field
    fst : I
    snd : I→S fst

_×_ : (S T : Set) → Set
S × T = Σ S (λ _ → T)

_and_ : Bool → Bool → Bool
false and b = false
true  and b = b

infixr 3 _and_

_or_ : Bool → Bool → Bool
true  or b = true
false or b = b

infixr 2 _or_

not : Bool → Bool
not false = true
not true  = false

vecany : ∀{n} → {A : Set} → (A → Bool) → Vec A n → Bool
vecany f [] = false
vecany f (x ∷ xs) = f x or vecany f xs
