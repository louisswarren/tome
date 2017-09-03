module eden where

data Formula : Set where
  P : Formula
  Q : Formula
  _⇒_ : Formula → Formula → Formula
--
-- data Deduction : Set where
--   Assumption : Formula → Deduction
--   ArrowIntro : Deduction → Formula → Deduction
--   ArrowElim  : Deduction → Deduction → Deduction
--
-- Resolve : Deduction → Formula
-- Resolve (Assumption a) = a
-- Resolve (ArrowIntro gamma phi) = (Resolve gamma) ⇒ phi
-- Resolve (ArrowElim gamma delta) =

data Deduction : Set₁ where
  Assuption  : Set → Deduction
  ArrowIntro : (Gamma : Deduction) → (A : Set) → Deduction
  ArrowElim  : {A B : Set} → (A → B) → A → Deduction

Resolve : Deduction → Set
Resolve (Assuption phi) = phi
Resolve (ArrowIntro gamma phi) = (Resolve gamma) → phi
Resolve (ArrowElim arrow phi) = (arrow phi)
