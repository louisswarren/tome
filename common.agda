module common where


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

_and_ : Bool → Bool → Bool
false and _ = false
true and b  = b

not : Bool → Bool
not true  = false
not false = true


----------------------------------------

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}


_==_ : ℕ → ℕ → Bool
zero ==  zero      = true
(suc n) == (suc m) = n == m
_ == _             = false


----------------------------------------

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A


[_] : {A : Set} → A → List A
[ x ] = x :: []

_++_ : {A : Set} → List A → List A → List A
[] ++ ys        = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 10 _++_
infixr 20 _::_

all : {A : Set} → (A → Bool) → List A → Bool
all _ []        = true
all f (x :: xs) = (f x) and (all f xs)


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
