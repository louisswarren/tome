module Texify where

open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Deduction
open import Formula
open import common

_>>_ = primStringAppend
infixr 1 _>>_

printlist : {A : Set} → String → (A → String) → List A → String
printlist delim f [] = ""
printlist delim f (x ∷ []) = f x
printlist delim f (x ∷ xs@(_ ∷ _)) = f x >> delim >> printlist delim f xs

lp = "\\left("
rp = "\\right)"

wrap : String → String
wrap s = "{" >> s >> "}"

texvar : Variable → String
texvar (mkvar s) = s

texterm : Term → String
textermvec : ∀{n} → Vec Term n → String

texterm (varterm x) = wrap (texvar x)
texterm (functerm (mkfunc n f) ts) with n
...                              | zero = wrap f
...                              | suc _ = wrap (f >> lp >> textermvec ts >> rp)

textermvec [] = ""
textermvec (t ∷ []) = texterm t
textermvec (t ∷ ts@(_ ∷ _)) = texterm t >> ", " >> textermvec ts


texformula : Formula → String

parenformula : Formula → String
parenformula p@(atom _ _) = texformula p
parenformula p@(_ ⇒ b) with formulacmp b ⊥
...                    | false = lp >> texformula p >> rp
...                    | true = texformula p
parenformula p@(_ ∧ _) = lp >> texformula p >> rp
parenformula p@(_ ∨ _) = lp >> texformula p >> rp
parenformula p@(Λ _ _) = texformula p
parenformula p@(V _ _) = texformula p

--``texformula (atom (mkrel n f) ts) | false with n
--``...                                      | zero        = f
--``...                                      | suc zero    = f >> textermvec ts
--``...                                      | suc (suc _) = f >> lp
--``                                                         >> textermvec ts >> rp

texformula a@(atom f ts) with formulacmp a ⊥
...                              | true = "\\bot"
texformula (atom (mkrel n f) ts) | false with n
...                                      | zero = f
...                                      | suc zero = f >> textermvec ts
texformula (atom (mkrel n f) (x ∷ y ∷ []))
                                 | false | suc (suc zero)
                                                   = texterm x >> f >> texterm y
...                                      | suc (suc _) = f >> lp
                                                         >> textermvec ts >> rp
texformula (a ⇒ b) with formulacmp b ⊥
...           | false = parenformula a >> " \\Tarrow " >> parenformula b
...           | true  = "\\Tneg{" >> parenformula a >> "}"
texformula (a ∧ b) = parenformula a >> " \\Tand " >> parenformula b
texformula (a ∨ b) = parenformula a >> " \\Tor " >> parenformula b
texformula (Λ x a) = "\\Tforall_{" >> texvar x >> "} " >> parenformula a
texformula (V x a) = "\\Texists_{" >> texvar x >> "} " >> parenformula a

texformulae : List Formula → String
texformulae forms = printlist ", " texformula forms

texdeduction : ∀{Ω Γ α} → Ω , Γ ⊢ α → String
texdeduction {Ω} {Γ} {α} d = "$"
                             >> texformulae Γ
                             >> " \\vdash_{"
                                >> printlist ", " Scheme.name Ω
                                >> "} "
                             >> texformula α >> "$"

data Textree : Set where
  cut         : ∀{Ω Γ α} → Ω , Γ ⊢ α → Textree
  openax      : Formula → Textree
  closedax    : Formula → String → Textree
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

cuttex : ∀{Ω Γ α} → Ω , Γ ⊢ α → String
cuttex {Ω} {Γ} {α} d = tag "UnaryInfC" (texdeduction d)

texifytree : ℕ → Textree → String
texifytree i (cut d)                  = line i "\\AxiomC{}"
                                        >> line i (cuttex d)
texifytree i (openax x)               = inf i "AxiomC" x
texifytree i (closedax x s) with (primStringEquality s "")
...                         | false   = line i "\\AxiomC{}"
                                        >> label i s
                                        >> inf i "UnaryInfC" x
...                         | true    = line i "\\AxiomC{}"
                                        >> inf i "UnaryInfC" x
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



dtot : ∀{α Γ} → {Ω : List Scheme}  → List Formula → Ω , Γ ⊢ α → Textree
dtot {α} o (lemma d)           = cut d
dtot {α} {_} {Ω} o (axiom n {pf} v)     = closedax α (Scheme.name ((Ω ! n) {pf}))
dtot {α} o (assume a) with (membership formulacmp a o)
...                   | false  = closedax   α ""
...                   | true   = openax     α
dtot {α} o (arrowintro a d)    = unaryinf   α "\\Tarrowintro" (dtot o d)
dtot {α} o (arrowelim d₁ d₂)   = binaryinf  α "\\Tarrowelim"  (dtot o d₁)
                                                                   (dtot o d₂)
dtot {α} o (conjintro d₁ d₂)   = binaryinf  α "\\Tconjintro"  (dtot o d₁)
                                                                   (dtot o d₂)
dtot {α} o (conjelim d₁ d₂)    = binaryinf  α "\\Tconjelim"   (dtot o d₁)
                                                                   (dtot o d₂)
dtot {α} o (disjintro₁ b d)    = unaryinf   α "\\Tdisjintro"  (dtot o d)
dtot {α} o (disjintro₂ a d)    = unaryinf   α "\\Tdisjintro"  (dtot o d)
dtot {α} o (disjelim d₁ d₂ d₃) = trinaryinf α "\\Tdisjelim"   (dtot o d₁)
                                                                   (dtot o d₂)
                                                                   (dtot o d₃)
dtot {α} o (univintro x d)     = unaryinf   α "\\Tunivintro"  (dtot o d)
dtot {α} o (univelim r d)      = unaryinf   α "\\Tunivelim"   (dtot o d)
dtot {α} o (existintro r x d)  = unaryinf   α "\\Texistintro" (dtot o d)
dtot {α} o (existelim d₁ d₂)   = binaryinf  α "\\Texistelim"  (dtot o d₁)
                                                                   (dtot o d₂)

texify : ∀{Γ Ω α} → Ω , Γ ⊢ α → String
texify {Γ} d = texifytree 0 (dtot Γ d)

texifyded : ∀{Ω Γ α} → Ω , Γ ⊢ α → String
texifyded d = "\\begin{deduction}\n"
              >> texify d
              >> "\\end{deduction}\n"

texifypf : ∀{Ω Γ α} → Ω , Γ ⊢ α → String
texifypf d = "\\begin{proof}\n"
             >> "\\begin{deduction}\n"
             >> texify d
             >> "\\end{deduction}\n"
             >> "\\end{proof}\n"

texifypfs : ∀{Ω₁ Ω₂ Γ₁ Γ₂ α₁ α₂} → Ω₁ , Γ₁ ⊢ α₁ → Ω₂ , Γ₂ ⊢ α₂ →  String
texifypfs d₁ d₂ = "\\begin{proof}\n"
                  >> "$(\\implies)$\n"
                  >> "\\begin{deduction}[nonfinal]\n"
                  >> texify d₁
                  >> "\\end{deduction}\n"
                  >> "\\begin{deduction}\n"
                  >> texify d₂
                  >> "\\end{deduction}\n"
                  >> "\\end{proof}\n"


texifyreducewith : ∀ As B xs → String → (As ⊃ B) xs → String
texifyreducewith As B xs s d = "\\begin{proposition} "
                                    >> "\\label{prop:"
                                    >> printlist "," Scheme.name As
                                    >> "->" >> Scheme.name B >> "}\n"
                                  >> "$\\" >> printlist "s, \\" Scheme.name As
                                  >> "s \\reduces \\" >> Scheme.name B  >> "s$"
                                  >> "\n"
                                  >> "\\begin{proof}\n"
                                  >> s
                                  >> texifyded d
                                  >> "\\end{proof}\n"
                                  >> "\\end{proposition}\n"

texifyreduce : ∀ As B xs → (As ⊃ B) xs → String
texifyreduce As B xs d = texifyreducewith As B xs "" d

texifyequivalence : ∀{A B xs ys} → ([ A ] ⊃ B) xs → ([ B ] ⊃ A) ys → String
texifyequivalence {A} {B} d₁ d₂ = "\\begin{proposition} "
                                    >> "\\label{prop:"
                                    >> Scheme.name A >> "=" >> Scheme.name B
                                    >> "}\n"
                                  >> "$\\" >> Scheme.name A
                                  >> "s \\reduces \\" >> Scheme.name B  >> "s$"
                                  >> " and "
                                  >> "$\\" >> Scheme.name B
                                  >> "s \\reduces \\" >> Scheme.name A  >> "s$"
                                  >> "\\n"
                                  >> texifypfs d₁ d₂
                                  >> "\\end{proposition}\n"

quicktexify : ∀{Ω Γ α} → Ω , Γ ⊢ α → String
quicktexify d = "\\documentclass[landscape]{article}\n"
             >> "\\usepackage[a4paper,margin=0.5in,landscape]{geometry}\n"
             >> "\\newcommand{\\Tarrowintro}{$\\rightarrow$I}\n"
             >> "\\newcommand{\\Tarrowelim}{$\\rightarrow$E}\n"
             >> "\\newcommand{\\Tconjintro}{$\\land$I}\n"
             >> "\\newcommand{\\Tconjelim}{$\\land$E}\n"
             >> "\\newcommand{\\Tdisjintro}{$\\lor$I}\n"
             >> "\\newcommand{\\Tdisjelim}{$\\lor$E}\n"
             >> "\\newcommand{\\Tunivintro}{$\\forall$I}\n"
             >> "\\newcommand{\\Tunivelim}{$\\forall$E}\n"
             >> "\\newcommand{\\Texistintro}{$\\exists$I}\n"
             >> "\\newcommand{\\Texistelim}{$\\exists$E}\n"
             >> "\\newcommand{\\Tarrow}{\\rightarrow}\n"
             >> "\\newcommand{\\Tand}{\\land}\n"
             >> "\\newcommand{\\Tor}{\\lor}\n"
             >> "\\newcommand{\\Tforall}{\\forall}\n"
             >> "\\newcommand{\\Texists}{\\exists}\n"
             >> "\\newcommand{\\Tneg}{\\lnot}\n"
             >> "\\usepackage{bussproofs}\n"
             >> "\\begin{document}\n"
             >> texify d
             >> "\\end{document}\n"
