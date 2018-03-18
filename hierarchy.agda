open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Deduction

open import common

record Branch (A : Set) : Set where
  constructor branch
  field
    stem : A
    leaves : List A

_∈ℕ_ : ℕ → List ℕ → Bool
a ∈ℕ [] = false
a ∈ℕ (x ∷ xs) with (a == x)
...            | false = a ∈ℕ xs
...            | true = true

_⊂ℕ_ : List ℕ → List ℕ → Bool
xs ⊂ℕ ys = all (λ n → n ∈ℕ ys) xs

explode : Branch ℕ → List ℕ → List ℕ
explode (branch stem leaves) xs with (leaves ⊂ℕ xs)
...                             | false = []
...                             | true = stem ∷ []

explodeall : List (Branch ℕ) → List ℕ → List ℕ
explodeall [] xs = xs
explodeall (branch stem _ ∷ bs) xs  with stem ∈ℕ xs
explodeall (b@(branch _ _) ∷ bs) xs | false = explode b xs ++ explodeall bs xs
explodeall (branch stem _ ∷ bs) xs  | true = explodeall bs xs

{-# TERMINATING #-}
clhelp : List (Branch ℕ) → List ℕ → List ℕ → List ℕ
clhelp bs xs exs with (len xs < len exs)
clhelp bs xs exs | false = xs
clhelp bs xs exs | true = clhelp bs exs (explodeall bs exs)

closure : List (Branch ℕ) → List ℕ → List ℕ
closure bs xs = clhelp bs xs (explodeall bs xs)


-- proofs : List (Branch ℕ)
-- proofs =
--    branch 4 (3 ∷ []) ∷
--    branch 4 (6 ∷ []) ∷
--    branch 3 (3 ∷ []) ∷
--    branch 3 (3 ∷ []) ∷
--    branch 3 (9 ∷ []) ∷
--    branch 3 (9 ∷ []) ∷
--    branch 7 (5 ∷ []) ∷
--    branch 7 (9 ∷ []) ∷
--    branch 8 (6 ∷ []) ∷
--    branch 8 (10 ∷ []) ∷
--    branch 7 (10 ∷ []) ∷
--    branch 10 (5 ∷ []) ∷
--    branch 4 (10 ∷ []) ∷
--    branch 11 (5 ∷ []) ∷
--    branch 11 (6 ∷ []) ∷
--    branch 4 (11 ∷ []) ∷
--    branch 7 (10 ∷ []) ∷
--    branch 4 (8 ∷ []) ∷
--    branch 7 (9 ∷ []) ∷
--    branch 8 (9 ∷ []) ∷
--    branch 8 (3 ∷ []) ∷
--    branch 9 (5 ∷ 3 ∷ []) ∷
--    branch 10 (6 ∷ 7 ∷ []) ∷
--    branch 3 (6 ∷ 3 ∷ []) ∷
--    branch 7 (7 ∷ []) ∷
--    branch 7 (7 ∷ []) ∷
--    branch 10 (7 ∷ 8 ∷ []) ∷
--    branch 9 (3 ∷ 10 ∷ []) ∷
--    branch 1 (5 ∷ []) ∷
--    branch 9 (3 ∷ 1 ∷ []) ∷
--    branch 2 (1 ∷ []) ∷
--    branch 2 (10 ∷ []) ∷
--    []
-- 
-- testcl : List ℕ
-- testcl = closure proofs (5 ∷ [])
