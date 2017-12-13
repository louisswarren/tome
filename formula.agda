open import common

module formula where


-- Relation symbols

data _-aryRelationSymbol : ℕ → Set where
  _-aryrelationsymbol_ : (n : ℕ) → String → (n)-aryRelationSymbol

Propsymbol = (zero)-aryRelationSymbol
propsymbol : String → Propsymbol
propsymbol s = (zero)-aryrelationsymbol s


-- Terms

data _-aryFunctionSymbol : ℕ → Set where
  _-aryfunctionsymbol_ : (n : ℕ) → String → (n)-aryFunctionSymbol

ConstantSymbol = (zero)-aryFunctionSymbol
constantsymbol : String → ConstantSymbol
constantsymbol s = (zero)-aryfunctionsymbol s

data Variable : Set where
  variable : String → Variable

data Term : Set where
  variableterm : Variable → Term
  functionterm : ∀{n} → (n)-aryFunctionSymbol → Vector Term n → Term

constantterm : ConstantSymbol → Term
constantterm t = functionterm t []


-- Formulae

data Formula : Set where
  atomic : ∀{n} → (n)-aryRelationSymbol → Vector Term n → Formula
  _⇒_    : Formula → Formula → Formula
  _∧_    : Formula → Formula → Formula
  _∨_    : Formula → Formula → Formula
  ∀[_]_  : Variable → Formula → Formula
  ∃[_]_  : Variable → Formula → Formula

infixr 110 _∨_
infixr 120 _∧_
infixr 130 _⇒_


-- Relations and functions

Proposition = Formula
proposition : String → Proposition
proposition s = (atomic (propsymbol s) ([]))

Predicate = Term → Formula
predicate : String → Predicate
predicate s = λ σ → (atomic ((1)-aryrelationsymbol s) (σ ∷ []))

BinaryRelation = Term → Term → Formula
binaryrelation : String → BinaryRelation
binaryrelation s = λ σ → (λ τ → (atomic ((2)-aryrelationsymbol s) (σ ∷ τ ∷ [])))



Constant = Term
constant : String → Constant
constant s = constantterm (constantsymbol s)

UnaryFunction = Term → Term
unaryfunction : String → UnaryFunction
unaryfunction s = λ n → (functionterm ((1)-aryfunctionsymbol s) (n ∷ []))

BinaryFunction = Term → Term → Term
binaryfunction : String → BinaryFunction
binaryfunction s = λ n → (λ m → (functionterm ((2)-aryfunctionsymbol s) (n ∷ m ∷ [])))

-- Examples

x y : Term
x = variableterm (variable "x")
y = variableterm (variable "y")

∀x ∃x ∀y ∃y : Formula → Formula
∀x a = ∀[ variable "x" ] a
∃x a = ∃[ variable "x" ] a
∀y a = ∀[ variable "y" ] a
∃y a = ∃[ variable "y" ] a

s t : Term
s = constant "s"
t = constant "t"

f = binaryfunction "f"

P : Predicate
P = predicate "P"

Q : Proposition
Q = proposition "Q"

R : BinaryRelation
R = binaryrelation "R"


α : Formula
α = ∀x (P x) ∨ ∃y (∀x (R x t) ⇒ Q) ∧ (P (f t y) ∨ (R x x))
