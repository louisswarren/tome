open import common
open import formula
open import deduction

module texify where

texformula : Formula → String
texsubformula : Formula → String

texformula (atom n) = n
texformula (pred n (term t)) = n >> t
texformula (p ⇒ q) with (q ≡ ⊥)
...                   | true  = "\\lnot " >> (texsubformula p)
...                   | false = (texsubformula p) >> " \\mimp " >> (texsubformula q)
texformula (p ∧ q) = (texsubformula p) >> " \\mand " >> (texsubformula q)
texformula (p ∨ q) = (texsubformula p) >> " \\mor " >> (texsubformula q)
texformula (Α (term t) p) = "\\forall_{" >> t >> "}" >> (texsubformula p)
texformula (Ε (term t) p) = "\\exists_{" >> t >> "}" >> (texsubformula p)

texsubformula f@(atom n)   = texformula f
texsubformula f@(pred n t) = texformula f
texsubformula f@(Α _ _)    = texformula f
texsubformula f@(Ε _ _)    = texformula f
texsubformula f@(_ ⇒ q) with (q ≡ ⊥)
...                        | true  = texformula f
...                        | false = "(" >> texformula f >> ")"
texsubformula p          = "(" >> texformula p >> ")"

texroot : ∀{Γ p} → ℕ → Deduction Γ p → String → String
texroot 1 T rule = "\\RightLabel{" >> rule >> "}\n" >>
                   "\\UnaryInfC{$" >> texformula (conclusion T) >> "$}\n"
texroot 2 T rule = "\\RightLabel{" >> rule >> "}\n" >>
                   "\\BinaryInfC{$" >> texformula (conclusion T) >> "$}\n"
texroot 3 T rule = "\\RightLabel{" >> rule >> "}\n" >>
                   "\\TernaryInfC{$" >> texformula (conclusion T) >> "$}\n"
texroot _ T rule = ""



texify' : ∀{Γ p} → Deduction Γ p → List Formula → String
texify' d@(Assume p)          Γ with (p ∈ Γ)
...                                | true  = "\\AxiomC{$"
                                             >> texformula p
                                             >> "$}\n"
...                                | false = "\\AxiomC{[$"
                                             >> texformula p
                                             >> "$]}\n"
texify' d@(ArrowIntro T _)    Γ = (texify' T Γ) >> texroot 1 d "\\ndii"
texify' d@(ArrowElim T₁ T₂)   Γ = (texify' T₁ Γ)
                                  >> (texify' T₂ Γ)
                                  >> texroot 2 d "\\ndie"
texify' d@(ConjIntro T₁ T₂)   Γ = (texify' T₁ Γ)
                                  >> (texify' T₂ Γ)
                                  >> texroot 2 d "\\ndci"
texify' d@(ConjElim T₁ T₂)    Γ = (texify' T₁ Γ)
                                  >> (texify' T₂ Γ)
                                  >> texroot 2 d "\\ndce"
texify' d@(DisjIntro₁ T _)    Γ = (texify' T Γ) >> texroot 1 d "\\nddi"
texify' d@(DisjIntro₂ T _)    Γ = (texify' T Γ) >> texroot 1 d "\\nddi"
texify' d@(DisjElim T₁ T₂ T₃) Γ = (texify' T₁ Γ)
                                  >> (texify' T₂ Γ)
                                  >> (texify' T₃ Γ)
                                  >> texroot 2 d "\\ndce"
texify' d@(UniGIntro T _)     Γ = (texify' T Γ) >> texroot 1 d "\\ndfi"
texify' d@(UniGElim _ T)      Γ = (texify' T Γ) >> texroot 1 d "\\ndfe"
texify' d@(ExiGIntro T _)     Γ = (texify' T Γ) >> texroot 1 d "\\ndei"
texify' d@(ExiGElim _ T₁ T₂)  Γ = (texify' T₁ Γ)
                                  >> (texify' T₂ Γ)
                                  >> texroot 2 d "\\ndee"

texify : ∀{Γ p} → Deduction Γ p → String
texify d = "\\begin{prooftree}\n"
           >> texify' d (assumptions d) >> "\n"
           >> "\\end{prooftree}"

