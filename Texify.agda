module Texify where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Decidable hiding (⊥ ; ¬_)
open import Deduction
open import Formula
open import List
open import Vec
open import sugar


-- String manipulation
_>>_ = primStringAppend
infixr 1 _>>_

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

private
  -- We assume that all schemes are derivable, and will derive their instances
  -- by citing the schemes.
  postulate provescheme : (s : Scheme) → Derivable s
  proveschemes : (ss : List Scheme) → List.All Derivable ss
  proveschemes [] = []
  proveschemes (x ∷ ss) = provescheme x ∷ proveschemes ss

texterm : Term → String
textermvec : ∀{n} → Vec Term n → String

texterm (varterm x) = wrap (strvar x)
texterm (functerm (mkfunc n f) ts) with n
...                              | zero  = wrap (strfunc (mkfunc n f))
...                              | suc _ = wrap (strfunc (mkfunc n f)
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

--``texformula (atom (mkrel n f) ts) | false with n
--``...                                      | zero        = f
--``...                                      | suc zero    = f >> textermvec ts
--``...                                      | suc (suc _) = f >> lp
--``                                                         >> textermvec ts >> rp

texformula a@(atom f ts) with formulaEq a ⊥
...                              | yes _ = "\\bot"
texformula (atom (mkrel n k) ts) | no _  with k
...                                      | zero     = strrel (mkrel n k)
...                                      | suc zero = strrel (mkrel n k)
                                                      >> textermvec ts
texformula (atom (mkrel n k) (x ∷ y ∷ []))
                                 | no _  | suc (suc zero)
                                                   = texterm x >> strrel (mkrel n k) >> texterm y
...                                      | suc (suc _) = strrel (mkrel n k)  >> lp
                                                         >> textermvec ts >> rp
texformula (a ⇒ b) with formulaEq b ⊥
...           | yes _  = "\\Tneg{" >> parenformula a >> "}"
...           | no _  = parenformula a >> " \\Tarrow " >> parenformula b
texformula (a ∧ b) = parenformula a >> " \\Tand " >> parenformula b
texformula (a ∨ b) = parenformula a >> " \\Tor " >> parenformula b
texformula (Λ x a) = "\\Tforall_{" >> strvar x >> "} " >> parenformula a
texformula (V x a) = "\\Texists_{" >> strvar x >> "} " >> parenformula a

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

texifytree : ℕ → Textree → String
texifytree i (schemeax x s)           = line i ("\\AxiomC{}")
                                        >> label i s
                                        >> inf i "UnaryInfC" x
texifytree i (openax x)               = inf i "AxiomC" x
texifytree i (closedax x)             = line i (tag "AxiomC"
                                                ("[$" >> texformula x >> "$]"))
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


dtot : ∀{α Γ} → List Formula → Γ ⊢ α → Textree
dtot {α} o (cite s d)           = schemeax α s
dtot {α} o (assume a) with List.decide∈ formulaEq a o
...                   | yes _   = openax     α
...                   | no  _   = closedax   α
dtot {α} o (arrowintro a d)     = unaryinf   α "\\Tarrowintro" (dtot o d)
dtot {α} o (arrowelim d₁ d₂)    = binaryinf  α "\\Tarrowelim"  (dtot o d₁)
                                                                    (dtot o d₂)
dtot {α} o (conjintro d₁ d₂)    = binaryinf  α "\\Tconjintro"  (dtot o d₁)
                                                                    (dtot o d₂)
dtot {α} o (conjelim d₁ d₂)     = binaryinf  α "\\Tconjelim"   (dtot o d₁)
                                                                    (dtot o d₂)
dtot {α} o (disjintro₁ b d)     = unaryinf   α "\\Tdisjintro"  (dtot o d)
dtot {α} o (disjintro₂ a d)     = unaryinf   α "\\Tdisjintro"  (dtot o d)
dtot {α} o (disjelim d₁ d₂ d₃)  = trinaryinf α "\\Tdisjelim"   (dtot o d₁)
                                                                    (dtot o d₂)
                                                                    (dtot o d₃)
dtot {α} o (univintro x _ d)    = unaryinf   α "\\Tunivintro"  (dtot o d)
dtot {α} o (univelim r d)       = unaryinf   α "\\Tunivelim"   (dtot o d)
dtot {α} o (existintro r x _ d) = unaryinf   α "\\Texistintro" (dtot o d)
dtot {α} o (existelim _ d₁ d₂)  = binaryinf  α "\\Texistelim"  (dtot o d₁)
                                                                    (dtot o d₂)
dtot {α} o (close _ d)          = dtot o d


texdeduction : ∀{Γ α} → Γ ⊢ α → String
texdeduction d = texifytree 0 (dtot [] d)

texreduce : {xs : List Scheme} {y : Scheme} → xs ⊃ y → Vec Formula (Scheme.arity y) → String
texreduce {xs} r αs = texdeduction (r (proveschemes xs) αs)
