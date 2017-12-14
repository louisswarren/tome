module common where

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

----------------------------------------

data Bool : Set where
  true  : Bool
  false : Bool
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

_or_ : Bool → Bool → Bool
true or _  = true
false or b = b
infixr 5 _or_

_and_ : Bool → Bool → Bool
false and _ = false
true and b  = b
infixr 10 _and_

not : Bool → Bool
not true  = false
not false = true


data False  : Set where
record True : Set where

isTrue : Bool → Set
isTrue true  = True
isTrue false = False



----------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}


_+_ : ℕ → ℕ → ℕ
0 + n = n
(suc n) + m = suc (n + m)


_==_ : ℕ → ℕ → Bool
zero ==  zero      = true
(suc n) == (suc m) = n == m
_ == _             = false


max : ℕ → ℕ → ℕ
max 0 m             = m
max n 0             = n
max (suc n) (suc m) = suc (max n m)

----------------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A


[_] : {A : Set} → A → List A
[ x ] = x ∷ []

_++_ : {A : Set} → List A → List A → List A
[] ++ ys        = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 10 _++_
infixr 20 _∷_

all : {A : Set} → (A → Bool) → List A → Bool
all _ []        = true
all f (x ∷ xs) = (f x) and (all f xs)

any : {A : Set} → (A → Bool) → List A → Bool
any _ []        = false
any f (x ∷ xs) = (f x) or (any f xs)

map : {A B : Set} → (A → B) → List A → List B
map _ []        = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

len : {A : Set} → List A → ℕ
len []        = zero
len (x ∷ xs) = suc (len xs)

----------------------------------------

data Vector (A : Set) : (n : ℕ) → Set where
  []   : Vector A 0
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (suc n)

_+/+_ : ∀{A n m} → Vector A n → Vector A m → Vector A (n + m)
[] +/+ ys        = ys
(x ∷ xs) +/+ ys = x ∷ (xs +/+ ys)


listtovec : {A : Set} → (xs : List A) → Vector A (len xs)
listtovec [] = []
listtovec (x ∷ xs) = x ∷ (listtovec xs)


----------------------------------------

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringAppend   : String → String → String
  primStringEquality : String → String → Bool
  primShowString     : String → String

_>>_ : String → String → String
_>>_ = primStringAppend

infixl 1 _>>_

_===_ : String → String → Bool
_===_ = primStringEquality

join : String → List String → String
join _     []                 = ""
join _     (x ∷ [])          = x
join delim (x ∷ xs@(y ∷ _)) = x >> delim >> (join delim xs)

