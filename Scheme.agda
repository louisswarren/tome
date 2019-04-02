module Scheme where

open import Agda.Builtin.String
open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Deduction
open import Formula
open import List
open import Texify
open import Vec

record Scheme : Set where
  constructor scheme
  field
    arity : ℕ
    inst  : Vec Formula arity → Formula


-- Easier constructors for schemes
nullaryscheme : Formula → Scheme
nullaryscheme f = scheme 0 λ { [] → f }

unaryscheme : (Formula → Formula) → Scheme
unaryscheme f = scheme 1 λ { (α ∷ []) → f α }

binaryscheme : (Formula → Formula → Formula) → Scheme
binaryscheme f = scheme 2 λ { (α ∷ β ∷ []) → f α β }


Derivable : Scheme → Set
Derivable S = ∀ αs → ⊢ (Scheme.inst S αs)

infix 1 _⊃_
_⊃_ : List Scheme → Scheme → Set
(Ω ⊃ Φ) = List.All (Derivable) Ω → Derivable Φ


-- We assume that all schemes are derivable, and will derive their instances
-- by citing the schemes.
texreduce : {xs : List Scheme} {y : Scheme} → xs ⊃ y
            → Vec Formula (Scheme.arity y) → String
texreduce {xs} r αs = texdeduction (r (proveschemes xs) αs)
  where
    postulate provescheme : (s : Scheme) → Derivable s
    proveschemes : (ss : List Scheme) → List.All Derivable ss
    proveschemes [] = []
    proveschemes (x ∷ ss) = provescheme x ∷ proveschemes ss
