module Texify where

open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Deduction
open import Formula
open import Vec

_>>_ = primStringAppend
infixr 1 _>>_

data Textree : Set where
  schemeax    : Formula → String → Textree
  openax      : Formula → Textree
  closedax    : Formula → String → Textree
  unaryinf    : Formula → String → Textree → Textree
  binaryinf   : Formula → String → Textree → Textree → Textree
  trinaryinf  : Formula → String → Textree → Textree → Textree → Textree



--line : ℕ → String → String
--line zero s = s >> "\n"
--line (suc n) s = "\t" >> line n s
--
--tag : String → String → String
--tag f s = "\\" >> f >> "{" >> s >> "}"
--
--label : ℕ → String → String
--label i s = line i (tag "RightLabel" s)
--
--inf : ℕ → String → Formula → String
--inf i s x = line i (tag s ("$" >> (texformula x) >> "$"))
--
--schemeaxtex : ∀{Γ α} → Γ ⊢ α → String
--schemeaxtex {Γ} {α} d = tag "UnaryInfC" (texdeduction d)
--
--texifytree : ℕ → Textree → String
--texifytree i (schemeax d)             = line i "\\AxiomC{}"
--                                        >> line i (schemeaxtex d)
--texifytree i (openax x)               = inf i "AxiomC" x
--texifytree i (closedax x s) with (primStringEquality s "")
--...                         | false   = line i "\\AxiomC{}"
--                                        >> label i s
--                                        >> inf i "UnaryInfC" x
--...                         | true    = line i "\\AxiomC{}"
--                                        >> inf i "UnaryInfC" x
--texifytree i (unaryinf x s T)         = texifytree i T
--                                        >> label i s
--                                        >> inf i "UnaryInfC" x
--texifytree i (binaryinf x s T₁ T₂)     = texifytree i T₁
--                                        >> texifytree (i + 1) T₂
--                                        >> label i s
--                                        >> inf i "BinaryInfC" x
--texifytree i (trinaryinf x s T₁ T₂ T₃) = texifytree i T₁
--                                        >> texifytree (i + 1) T₂
--                                        >> texifytree (i + 2) T₃
--                                        >> label i s
--                                        >> inf i "TrinaryInfC" x
--
--
--

postulate provescheme : (s : Scheme) → ∀ αs →  ⊢ (Scheme.inst s αs)

postulate
  texformula : Formula → String
  texdeduction : ∀{Γ α} → Γ ⊢ α → String


texreduce : (xs : List Scheme) → (y : Scheme) → xs ⊃ y → String
texreduce xs y x = {! -m   !}

uniquesymbols : (n : ℕ) → Vec Formula n
uniquesymbols zero = []
uniquesymbols (suc n) = atom (mkprop n) [] ∷ uniquesymbols n

texhalp : ∀ s t → (Derivable s → Derivable t) → String
texhalp s t r = texdeduction (r (provescheme s) (uniquesymbols (Scheme.arity t)))
