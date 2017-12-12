open import common

module formula where


-- Relations

data _-aryRelationSymbol : ℕ → Set where
  _-aryrelation_ : (n : ℕ) → String → (n)-aryRelationSymbol

Propsymbol = (zero)-aryRelationSymbol
propsymbol : String → Propsymbol
propsymbol s = (zero)-aryrelation s


-- Terms

data _-aryFunctionSymbol : ℕ → Set where
  _-aryfunction_ : (n : ℕ) → String → (n)-aryFunctionSymbol

Constant = (zero)-aryFunctionSymbol
constant : String → Constant
constant s = (zero)-aryfunction s

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
  ∃[_]_  : Formula → Variable → Formula
  ∀[_]_  : Formula → Variable → Formula


-- Examples

x = variable "x"
y = variable "y"

s = constant "s"
t = constant "t"

f = (2)-aryfunction "f"

P = (1)-aryrelation "P"
Q = propsymbol "Q"
R = (2)-aryrelation "R"


α = ∃[ x ] (P
