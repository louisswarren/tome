module common where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

data Inspect {A : Set}(x : A) : Set where
  with≡ : (y : A) → x ≡ y → Inspect x

inspect : {A : Set} → (x : A) → Inspect x
inspect x = with≡ x refl

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

[_] : {A : Set} → A → List A
[ x ] = x ∷ []

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 4 _++_

remove : {A : Set} → (A → A → Bool) → A → List A → List A
remove cmp y [] = []
remove cmp y (x ∷ xs) with cmp y x
...                   | false = x ∷ remove cmp y xs
...                   | true  = remove cmp y xs


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

vecmap : ∀{n} → {A B : Set} → (A → B) → Vec A n → Vec B n
vecmap f [] = []
vecmap f (x ∷ xs) = f x ∷ vecmap f xs

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

all : {A : Set} → (A → Bool) → List A → Bool
all f [] = true
all f (x ∷ xs) = f x and all f xs

any : {A : Set} → (A → Bool) → List A → Bool
any f [] = false
any f (x ∷ xs) = f x or any f xs

vecall : ∀{n} → {A : Set} → (A → Bool) → Vec A n → Bool
vecall f [] = true
vecall f (x ∷ xs) = f x and vecall f xs

vecany : ∀{n} → {A : Set} → (A → Bool) → Vec A n → Bool
vecany f [] = false
vecany f (x ∷ xs) = f x or vecany f xs


data False : Set where
record True : Set where

isTrue : Bool → Set
isTrue false = False
isTrue true  = True

membership : {A : Set} → (A → A → Bool) → A → List A → Bool
membership equality x xs = any (equality x) xs

Membership : {A : Set} → (A → A → Bool) → A → List A → Set
Membership equality x xs = isTrue (membership equality x xs)

len : {A : Set} → List A → ℕ
len [] = zero
len (_ ∷ xs) = suc (len xs)

_!_ : {A : Set} → (xs : List A) → (k : ℕ) → {_ : isTrue (k < (len xs))} → A
([] ! k) {()}
(x ∷ xs) ! zero = x
((x ∷ xs) ! suc k) {pf} = (xs ! k) {pf}

_!!_ : ∀{n} → {A : Set} → (xs : Vec A n) → (k : ℕ) → {_ : isTrue (k < n)} → A
([] !! k) {()}
(x ∷ xs) !! zero = x
((x ∷ xs) !! suc k) {pf} = (xs !! k) {pf}
