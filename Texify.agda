module Texify where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Decidable hiding (⊥ ; ¬_)
open import Deduction
open import Ensemble
open import Formula
open import List
open import Scheme
open import Vec
open import Sugar

TEXarrowintro = "$\\rightarrow^+$"
TEXarrowelim = "$\\rightarrow^-$"
TEXconjintro = "$\\land^+$"
TEXconjelim = "$\\land^-$"
TEXdisjintro = "$\\lor^+$"
TEXdisjelim = "$\\lor^-$"
TEXunivintro = "$\\forall^+$"
TEXunivelim = "$\\forall^-$"
TEXexistintro = "$\\exists^+$"
TEXexistelim = "$\\exists^-$"
TEXarrow = " \\rightarrow "
TEXand = " \\land "
TEXor = " \\lor "
TEXforall = "\\forall"
TEXexists = "\\exists"
TEXnot = "\\lnot"
TEXbot = "\\bot"

-- String manipulation
_>>_ = primStringAppend
infixr 1 _>>_

-- Instead of using stdlib
strnum : ℕ → String
strnum zero = "0"
strnum (suc n) = "s(" >> strnum n >> ")"

strrel : Relation → String
strrel (rel 0 k) = "\\bot"
strrel (rel 1 k) = "A"
strrel (rel 2 k) = "B"
strrel (rel 3 k) = "C"
strrel (rel 4 k) = "D"
strrel (rel 5 k) = "P"
strrel (rel 6 k) = "Q"
strrel (rel (suc (suc (suc (suc (suc (suc n)))))) k) = "R_" >> strnum n

strvar : Variable → String
strvar xvar = "x"
strvar yvar = "y"
strvar zvar = "z"
strvar (var n) = "v_" >> strnum n

-- The constants are the natural numbers
strfunc : Function → String
strfunc (func n k) = "f_" >> strnum n

join : String → List String → String
join delim [] = ""
join delim (s ∷ []) = s
join delim (s ∷ ss@(_ ∷ _)) = s >> delim >> join delim ss

joinmap : {A : Set} → String → (A → String) → List A → String
joinmap delim f [] = ""
joinmap delim f (x ∷ []) = f x
joinmap delim f (x ∷ xs@(_ ∷ _)) = f x >> delim >> joinmap delim f xs

lp = "\\left("
rp = "\\right)"

wrap : String → String
wrap s = "{" >> s >> "}"

texterm : Term → String
textermvec : ∀{n} → Vec Term n → String

texterm (varterm x) = wrap (strvar x)
texterm t0 = wrap "0"
texterm t1 = wrap "1"
texterm t2 = wrap "2"
texterm t3 = wrap "3"
texterm t4 = wrap "4"
texterm t5 = wrap "5"
texterm (functerm (func n f) ts) with n
...                              | zero  = wrap (strfunc (func n f))
...                              | suc _ = wrap (strfunc (func n f)
                                                 >> lp >> textermvec ts >> rp)

textermvec [] = ""
textermvec (t ∷ []) = texterm t
textermvec (t ∷ ts@(_ ∷ _)) = texterm t >> ", " >> textermvec ts


texformula : Formula → String

parenformula : Formula → String
parenformula p@(atom _ _) = texformula p
parenformula p@(_ ⇒ b) with formulaEq b ⊥
...                    | yes _ = texformula p
...                    | no _  = lp >> texformula p >> rp
parenformula p@(_ ∧ _) = lp >> texformula p >> rp
parenformula p@(_ ∨ _) = lp >> texformula p >> rp
parenformula p@(Λ _ _) = texformula p
parenformula p@(V _ _) = texformula p

texformula a@(atom f ts) with formulaEq a ⊥
...                            | yes _ = TEXbot
texformula (atom (rel n k) ts) | no _  with k
...                                    | zero     = strrel (rel n k)
...                                    | suc zero = strrel (rel n k)
                                                    >> textermvec ts
texformula (atom (rel n k) (x ∷ y ∷ []))
                               | no _  | suc (suc zero)
                                                 = texterm x >> strrel (rel n k) >> texterm y
...                                    | suc (suc _) = strrel (rel n k)  >> lp
                                                       >> textermvec ts >> rp
texformula (a ⇒ b) with formulaEq b ⊥
...           | yes _  = TEXnot >> wrap (parenformula a)
...           | no _  = parenformula a >> TEXarrow >> parenformula b
texformula (a ∧ b) = parenformula a >> TEXand >> parenformula b
texformula (a ∨ b) = parenformula a >> TEXor >> parenformula b
texformula (Λ x a) = TEXforall >> wrap(strvar x) >> parenformula a
texformula (V x a) = TEXexists >> wrap(strvar x) >> parenformula a

texformulae : List Formula → String
texformulae forms = joinmap ", " texformula forms


data Textree : Set where
  schemeax    : Formula → String → Textree
  openax      : Formula → Textree
  closedax    : Formula → Textree
  unaryinf    : Formula → String → Textree → Textree
  binaryinf   : Formula → String → Textree → Textree → Textree
  trinaryinf  : Formula → String → Textree → Textree → Textree → Textree


line : ℕ → String → String
line zero s = s >> "\n"
line (suc n) s = "\t" >> line n s

tag : String → String → String
tag f s = "\\" >> f >> "{" >> s >> "}"

label : ℕ → String → String
label i s = line i (tag "RightLabel" s)

inf : ℕ → String → Formula → String
inf i s x = line i (tag s ("$" >> (texformula x) >> "$"))

dis : ℕ → String → Formula → String
dis i s x = line i (tag s ("$\\left[" >> (texformula x) >> "\\right]$"))

texifytree : ℕ → Textree → String
texifytree i (schemeax x s)           = line i ("\\AxiomC{}")
                                        >> label i s
                                        >> inf i "UnaryInfC" x
texifytree i (openax x)               = inf i "AxiomC" x
texifytree i (closedax x)             = dis i "AxiomC" x
texifytree i (unaryinf x s T)         = texifytree i T
                                        >> label i s
                                        >> inf i "UnaryInfC" x
texifytree i (binaryinf x s T₁ T₂)     = texifytree i T₁
                                        >> texifytree (i + 1) T₂
                                        >> label i s
                                        >> inf i "BinaryInfC" x
texifytree i (trinaryinf x s T₁ T₂ T₃) = texifytree i T₁
                                        >> texifytree (i + 1) T₂
                                        >> texifytree (i + 2) T₃
                                        >> label i s
                                        >> inf i "TrinaryInfC" x


dtot : ∀{α Γ} {ω : Ensemble Formula} → Assembled formulaEq ω → Γ ⊢ α → Textree
dtot {α} o (cite s d)           = schemeax α s
dtot {α} o (assume a) with Ensemble.decide∈ a o
...                   | yes _   = openax     α
...                   | no  _   = closedax   α
dtot {α} o (arrowintro a d)     = unaryinf   α TEXarrowintro (dtot o d)
dtot {α} o (arrowelim d₁ d₂)    = binaryinf  α TEXarrowelim  (dtot o d₁)
                                                             (dtot o d₂)
dtot {α} o (conjintro d₁ d₂)    = binaryinf  α TEXconjintro  (dtot o d₁)
                                                             (dtot o d₂)
dtot {α} o (conjelim d₁ d₂)     = binaryinf  α TEXconjelim   (dtot o d₁)
                                                             (dtot o d₂)
dtot {α} o (disjintro₁ b d)     = unaryinf   α TEXdisjintro  (dtot o d)
dtot {α} o (disjintro₂ a d)     = unaryinf   α TEXdisjintro  (dtot o d)
dtot {α} o (disjelim d₁ d₂ d₃)  = trinaryinf α TEXdisjelim   (dtot o d₁)
                                                             (dtot o d₂)
                                                             (dtot o d₃)
dtot {α} o (univintro x _ d)    = unaryinf   α TEXunivintro  (dtot o d)
dtot {α} o (univelim r _ d)     = unaryinf   α TEXunivelim   (dtot o d)
dtot {α} o (existintro r x _ d) = unaryinf   α TEXexistintro (dtot o d)
dtot {α} o (existelim _ d₁ d₂)  = binaryinf  α TEXexistelim  (dtot o d₁)
                                                             (dtot o d₂)
dtot {α} o (close _ _ d)        = dtot o d


texdeduction : ∀{Γ α} → Γ ⊢ α → String
texdeduction d = "\\begin{prooftree}\n"
                 >> texifytree 0 (dtot (assembled-context d) d)
                 >> "\\end{prooftree}\n"


-- We postulate that every instance of the stronger schemes is derivable. By
-- using cite, the deductions for these become irrelevant, so a string is still
-- produced. Postulates are not safe, but here this should not cause problems,
-- since this can only be used to produce strings.

-- The scheme y can't be found implicitly because of how strings are defined.
texreduce : {xs : List Scheme}
            → (y : Scheme) → Vec Formula (Scheme.arity y) → xs ⊃ y → String
texreduce {xs} y αs xs⊃y = texdeduction (xs⊃y ⊢xs αs)
  where
    ⊢xs : (x : Scheme) → x List.∈ xs → Derivable x
    ⊢xs (scheme n name f) _ αs = cite name Ω
      where
        postulate Ω : ∅ ⊢ f αs

texprop : {xs : List Scheme}
            → (y : Scheme) → Vec Formula (Scheme.arity y) → xs ⊃ y → String
texprop {xs} y αs xs⊃y
  = "\\begin{proposition}\n"
    >> "$\\text{" >> joinmap "," Scheme.name xs >> "}"
       >> " \\supset \\text{" >> Scheme.name y >> "}$\n"
    >> "\\end{proposition}\n"
    >> "\\begin{proof}\n"
    >> "$ $\n"
    >> "\\vspace{-\\baselineskip}\n"
    >> (texreduce y αs xs⊃y)
    >> "\\vspace{-\\baselineskip}\n"
    >> "\\end{proof}\n"

