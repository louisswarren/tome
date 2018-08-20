module String where

open import Agda.Builtin.Bool
open import Agda.Builtin.String public
open import Agda.Builtin.TrustMe


open import Decidable

-- This is how the standard library does it too, sadly
stringEq : Decidable≡ String
stringEq s t with primStringEquality s t
...          | true = yes primTrustMe
...          | false = no φ
                       where postulate φ : (s ≢ t)
