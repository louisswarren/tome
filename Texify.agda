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



texformula : Formula → String

parenformula : Formula → String
parenformula p@(atom _ _) = texformula p
parenformula p@(_ ⇒ _) = lp >> texformula p >> rp
parenformula p@(_ ∧ _) = lp >> texformula p >> rp
parenformula p@(_ ∨ _) = lp >> texformula p >> rp
parenformula p@(Λ _ _) = texformula p
parenformula p@(V _ _) = texformula p



texformula (atom (mkrel n f) ts) with n
...                              | zero  = f
...                              | suc _ = f >> lp >> textermvec ts >> rp
texformula (a ⇒ b) = parenformula a >> " \\Timp " >> parenformula b
texformula (a ∧ b) = parenformula a >> " \\Tand " >> parenformula b
texformula (a ∨ b) = parenformula a >> " \\Tor " >> parenformula b
texformula (Λ x a) = "\\Tforall_{" >> texvar x >> "} " >> parenformula a
texformula (V x a) = "\\Texists_{" >> texvar x >> "} " >> parenformula a



texdeduction : ∀{Ω Γ α} → Ω , Γ ⊢ α → String
texdeduction d = ?

