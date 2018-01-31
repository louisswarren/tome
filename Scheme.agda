module Scheme where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Formula
open import common


record Σ (S : Set)(T : S → Set) : Set where
  constructor _↦_
  field
    fst : S
    snd : T fst

record _-aryScheme (n : ℕ) : Set where
  field
    name : String
    func : (Vec Formula n) → Formula


ΣScheme : Set
ΣScheme = Σ ℕ _-aryScheme

