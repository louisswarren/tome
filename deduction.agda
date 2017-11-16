open import common
open import formula

module deduction where


data Proof : List Formula → Formula →  Set
data Deduction : List Formula → Formula → Set

data Deduction where

conclusion : ∀{α Γ} → Deduction Γ α → Formula
conclusion {α} _ = α

assumptions : ∀{Γ α} → Deduction Γ α → List Formula
assumptions {Γ} _ = Γ


data Proof where
  proof : ∀{Γ α} → String → Deduction Γ α → Proof Γ α
