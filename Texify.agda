open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Deduction
open import Formula
open import common

_>>_ = primStringAppend
infixr 1 _>>_

lp = "\\left("
rp = "\\right)"

texvar : Variable → String
texvar (mkvar s) = s

texterm : Term → String
textermvec : ∀{n} → Vec Term n → String

texterm (varterm x) = texvar x
texterm (functerm (mkfunc n f) ts) with n
...                                | zero = f
...                                | suc _ = lp >> textermvec ts >> rp

textermvec [] = ""
textermvec (t ∷ []) = texterm t
textermvec (t ∷ ts@(_ ∷ _)) = texterm t >> ", " >> textermvec ts



tform : Formula → String

parenformula : Formula → String
parenformula p@(atom _ _) = tform p
parenformula p@(_ ⇒ _) = lp >> tform p >> rp
parenformula p@(_ ∧ _) = lp >> tform p >> rp
parenformula p@(_ ∨ _) = lp >> tform p >> rp
parenformula p@(Λ _ _) = tform p
parenformula p@(V _ _) = tform p



tform (atom (mkrel n f) ts) with n
...                         | zero     = f
...                         | suc zero = f >> textermvec ts
...                         | suc _    = f >> lp >> textermvec ts >> rp
tform (a ⇒ b) with (formulacmp b ⊥)
...           | false = parenformula a >> " \\Timp " >> parenformula b
...           | true  = "\\Tneg" >> parenformula a
tform (a ∧ b) = parenformula a >> " \\Tand " >> parenformula b
tform (a ∨ b) = parenformula a >> " \\Tor " >> parenformula b
tform (Λ x a) = "\\Tforall_{" >> texvar x >> "} " >> parenformula a
tform (V x a) = "\\Texists_{" >> texvar x >> "} " >> parenformula a


indent : ℕ → String
indent zero = ""
indent (suc i) = "\\t" >> indent i

inf : ℕ → ℕ → Formula → String
inf i 0 α = indent i >> "\\AxiomC{" >> (tform α) >> "}\\n"
inf i 1 α = indent i >> "\\UnaryInfC{" >> (tform α) >> "}\\n"
inf i 2 α = indent i >> "\\Binary{" >> (tform α) >> "}\\n"
inf i 3 α = indent i >> "\\TrinaryInfC{" >> (tform α) >> "}\\n"
inf _ _ _ = ""

closed : ℕ → String
closed i = indent i >> "\\AxiomC{}\\n"

label : ℕ → String → String
label i s = indent i >> "\\RightLabel{" >> s >> "}\\n"

tded : ∀{α Ω Γ} → (List Formula) → ℕ → Ω , Γ ⊢ α → String
tded {α} o i (axiom _)           = closed i >> label i (tform α) >> inf i 1 α
tded {α} o i (assume _) with (membership formulacmp α o)
...                     | false  = closed i >> inf i 1 α
...                     | true   = inf i 0 α
tded {α} o i (arrowintro p d)    = tded o i d
                                       >> label i ("\\Tarrowintro" >> tform p)
                                       >> inf i 1 α
tded {α} o i (arrowelim d₁ d₂)   = tded o i d₁ >> tded o (i + 1) d₂
                                       >> label i "\\Tarrowelim"
                                       >> inf i 2 α
tded {α} o i (conjintro d₁ d₂)   = tded o i d₁ >> tded o (i + 1) d₂
                                       >> label i "\\Tconjintro"
                                       >> inf i 2 α
tded {α} o i (conjelim d₁ d₂)    = tded o i d₁ >> tded o (i + 1) d₂
                                       >> label i "\\Tconjelim"
                                       >> inf i 2 α
tded {α} o i (disjintro₁ b d)    = tded o i d
                                       >> label i "\\Tdisjintro"
                                       >> inf i 1 α
tded {α} o i (disjintro₂ a d)    = tded o i d
                                       >> label i "\\Tdisjintro"
                                       >> inf i 1 α
tded {α} o i (disjelim d₁ d₂ d₃) = {!   !}
tded {α} o i (univintro x d)     = {!   !}
tded {α} o i (univelim r d)      = {!   !}
tded {α} o i (existintro r x d)  = {!   !}
tded {α} o i (existelim d₁ d₂)   = {! tded o i d₁ >> tded o (i + 1) d₂ >> ? !}

