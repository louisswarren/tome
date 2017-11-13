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
texroot 0 _ _    = ""
texroot 1 T rule = "\\RightLabel{" >> rule >> "}\n" >>
                   "\\UnaryInfC{$" >> texformula (conclusion T) >> "$}\n"
texroot 2 T rule = "\\RightLabel{" >> rule >> "}\n" >>
                   "\\BinaryInfC{$" >> texformula (conclusion T) >> "$}\n"
texroot 3 T rule = "\\RightLabel{" >> rule >> "}\n" >>
                   "\\TernaryInfC{$" >> texformula (conclusion T) >> "$}\n"
texroot (suc n) T rule = "\\BinaryInfC{\\vdots}" >> texroot n T rule



join : String → List String → String
join _     []                 = ""
join _     (x :: [])          = x
join delim (x :: xs@(y :: _)) = x >> delim >> (join delim xs)

texify' : ∀{Γ p} → List Formula → Deduction Γ p → String

texdlmap : ∀{Γs αs} → List Formula → DeductionList Γs αs → List String
texdlmap _ []        = []
texdlmap Γ (T :: Ts) = (texify' Γ T) :: (texdlmap Γ Ts)

texify' Γ d@(Collapse Ts (proof name _)) = (join "\\n" (texdlmap Γ Ts))
                                           >> (texroot (lendl Ts) d name)
texify' Γ d@(Assume p)          with (p ∈ Γ)
...                                | true  = "\\AxiomC{$"
                                             >> texformula p
                                             >> "$}\n"
...                                | false = "\\AxiomC{[$"
                                             >> texformula p
                                             >> "$]}\n"
texify' Γ d@(ArrowIntro T _)    = (texify' Γ T) >> texroot 1 d "\\ndii"
texify' Γ d@(ArrowElim T₁ T₂)   = (texify' Γ T₁)
                                  >> (texify' Γ T₂)
                                  >> texroot 2 d "\\ndie"
texify' Γ d@(ConjIntro T₁ T₂)   = (texify' Γ T₁)
                                  >> (texify' Γ T₂)
                                  >> texroot 2 d "\\ndci"
texify' Γ d@(ConjElim T₁ T₂)    = (texify' Γ T₁)
                                  >> (texify' Γ T₂)
                                  >> texroot 2 d "\\ndce"
texify' Γ d@(DisjIntro₁ T _)    = (texify' Γ T) >> texroot 1 d "\\nddi"
texify' Γ d@(DisjIntro₂ T _)    = (texify' Γ T) >> texroot 1 d "\\nddi"
texify' Γ d@(DisjElim T₁ T₂ T₃) = (texify' Γ T₁)
                                  >> (texify' Γ T₂)
                                  >> (texify' Γ T₃)
                                  >> texroot 3 d "\\ndde"
texify' Γ d@(UnivIntro T _)     = (texify' Γ T) >> texroot 1 d "\\ndfi"
texify' Γ d@(UnivElim _ T)      = (texify' Γ T) >> texroot 1 d "\\ndfe"
texify' Γ d@(ExistIntro T _)    = (texify' Γ T) >> texroot 1 d "\\ndei"
texify' Γ d@(ExistElim _ T₁ T₂) = (texify' Γ T₁)
                                  >> (texify' Γ T₂)
                                  >> texroot 2 d "\\ndee"

texify : ∀{Γ p} → Deduction Γ p → String
texify d = "\\begin{prooftree}\n"
           >> texify' (assumptions d) d >> "\n"
           >> "\\end{prooftree}"

