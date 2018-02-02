module Scheme where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Formula
open import common

record Scheme : Set where
  field
    arity : ℕ
    name  : String
    func  : (Vec Formula arity) → Formula

