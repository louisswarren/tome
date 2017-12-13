open import common

module formula where


-- Relations

data _-aryRelationSymbol : ℕ → Set where
  _-aryrelationsymbol_ : (n : ℕ) → String → (n)-aryRelationSymbol

Propsymbol = (zero)-aryRelationSymbol
propsymbol : String → Propsymbol
propsymbol s = (zero)-aryrelationsymbol s

-- Terms

data _-aryFunctionSymbol : ℕ → Set where
  _-aryfunctionsymbol_ : (n : ℕ) → String → (n)-aryFunctionSymbol

Constant = (zero)-aryFunctionSymbol
constant : String → Constant
constant s = (zero)-aryfunctionsymbol s

data Variable : Set where
  variable : String → Variable

data Term : Set where
  variableTerm : Variable → Term
  functionTerm : ∀{n} → (n)-aryFunctionSymbol → Vector Term n → Term

constantTerm : Constant → Term
constantTerm t = functionTerm t []

-- Formulae

data Formula : Set where
  atomic : ∀{n} → (n)-aryRelationSymbol → Vector Term n → Formula
  _⇒_    : Formula → Formula → Formula
  _∧_    : Formula → Formula → Formula
  _∨_    : Formula → Formula → Formula
  ∃[_]_  : Variable → Formula → Formula
  ∀[_]_  : Variable → Formula → Formula

infixr 110 _∨_
infixr 120 _∧_
infixr 130 _⇒_


-- Syntax

Proposition = Formula
proposition : String → Proposition
proposition s = (atomic (propsymbol s) ([]))

Predicate = Term → Formula
predicate : String → Predicate
predicate s = λ σ → (atomic ((1)-aryrelationsymbol s) (σ ∷ []))

BinaryRelation = Term → Term → Formula
binaryrelation : String → BinaryRelation
binaryrelation s = λ σ → (λ τ → (atomic ((2)-aryrelationsymbol s) (σ ∷ τ ∷ [])))


-- Examples

x y : Term
x = variableTerm (variable "x")
y = variableTerm (variable "y")
∃x ∃y ∀x ∀y : Formula → Formula
∃x a = ∃[ variable "x" ] a
∃y a = ∃[ variable "y" ] a
∀x a = ∀[ variable "x" ] a
∀y a = ∀[ variable "y" ] a

s t : Term
s = constantTerm (constant "s")
t = constantTerm (constant "t")

f = (2)-aryfunctionsymbol "f"

P : Predicate
P = predicate "P"

Q : Proposition
Q = proposition "Q"

R : BinaryRelation
R = binaryrelation "R"


α : Formula
α = ∀x (P x) ∨ ∃y (∀x (R x t) ⇒ Q) ∧ (P t ∨ (R x x))
