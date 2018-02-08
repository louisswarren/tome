open import Agda.Builtin.List
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String

open import Deduction
open import Formula
open import Texify

open import common
open import sugar

-- Without loss of generality, assume that schemes are applied only to formulae
-- in which the schemes' quantifiers are not free.

GLPO GLPOA GMP WGMP DP HE DPN HEN DNSU DNSE UD IP : Variable → Scheme
LEM WLEM DGP : Scheme



lem wlem : Formula → Formula
lem  Φ = Φ ∨ ¬ Φ
wlem Φ = ¬ Φ ∨ ¬¬ Φ

LEM  = unaryscheme "LEM" lem
WLEM = unaryscheme "WLEM" wlem



dgp : Formula → Formula → Formula
dgp Φ Ψ  = (Φ ⇒ Ψ) ∨ (Ψ ⇒ Φ)

DGP = binaryscheme "DGP" dgp



glpo glpoa gmp wgmp : Variable → Formula → Formula
glpo  v f = ∀x ¬Φx ∨ ∃x Φx                   where Φx = f [! v / x ]; ¬Φx = ¬ Φx
glpoa v f = ∀x Φx ∨ ∃x ¬Φx                   where Φx = f [! v / x ]; ¬Φx = ¬ Φx
gmp   v f = ¬∀x Φx ⇒ ∃x ¬Φx                  where Φx = f [! v / x ]; ¬Φx = ¬ Φx
wgmp  v f = ¬∀x Φx ⇒ ¬¬(∃x ¬Φx)              where Φx = f [! v / x ]; ¬Φx = ¬ Φx

GLPO  v = unaryscheme "GLPO"  (glpo v)
GLPOA v = unaryscheme "GLPOA" (glpoa v)
GMP   v = unaryscheme "GMP"   (gmp v)
WGMP  v = unaryscheme "WGMP"  (wgmp v)



dp he dpn hen : Variable → Formula → Formula
dp  v f = ∃y(Φy ⇒ ∀x Φx)              where Φx = f [! v / x ]; Φy = f [! v / y ]
he  v f = ∃y(∃x Φx ⇒ Φy)              where Φx = f [! v / x ]; Φy = f [! v / y ]
dpn v f = dp v (¬ f)
hen v f = he v (¬ f)

DP  v = unaryscheme "DP"  (glpo v)
HE  v = unaryscheme "HE"  (glpo v)
DPN v = unaryscheme "DPN" (glpo v)
HEN v = unaryscheme "HEN" (glpo v)



dnsu dnse : Variable → Formula → Formula
dnsu v f = ∀x(¬¬ Φx) ⇒ ¬¬(∀x Φx)                         where Φx = f [! v / x ]
dnse v f = ¬¬(∃x Φx) ⇒ ∃x (¬¬ Φx)                        where Φx = f [! v / x ]

DNSU v = unaryscheme "DNSU" (glpo v)
DNSE v = unaryscheme "DNSE" (glpo v)



ud ip : Variable → Formula → Formula → Formula
ud v f Ψ = ∀x (Φx ∨ Ψ) ⇒ (∀x Φx ∨ Ψ)                     where Φx = f [! v / x ]
ip v f Ψ = (Ψ ⇒ ∃x Φx) ⇒ ∃x(Ψ ⇒ Φx)                      where Φx = f [! v / x ]

UD v = binaryscheme "UD" (ud v)
IP v = binaryscheme "IP" (ud v)



