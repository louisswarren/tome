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


-- Partition members of A by their values of f
indexed : ∀{A B} → (f : A → B) → B → Set
indexed {A} f b = Σ A λ a → f a ≡ b


Partition : ∀{A B} → (A → B) → Set
Partition {_} {B} f = Σ B (indexed f)

-- A type A is isomorphic to its partition under any function

classify : ∀{A B} → (f : A → B) → A → Partition f
classify f a = f a , (a , refl)


extract : ∀{A B}{f : A → B} → Partition f → A
extract (b , (a , pf)) = a


isom₁ : ∀{A B} → (f : A → B) → (a : A) → extract (classify f a) ≡ a
isom₁ f a = refl

isom₂ : ∀{A B} → (f : A → B) → (α : Partition f) → classify f (extract α) ≡ α
isom₂ f (.(f a) , (a , refl)) = refl


-- Sdrawkcab?

data _-tree : ℕ → Set

Σtree = Σ ℕ _-tree

depth : List Σtree → ℕ

data _-tree where
  leaf : ℕ → (zero)-tree
  node : ℕ → (ts : List Σtree) → (depth ts)-tree

depth [] = zero
depth ((n , t) ∷ ts) = maxℕ n (depth ts)

dedepth : ∀{n} → (n)-tree → ℕ
dedepth {n} _ = n

wtf = Partition dedepth
