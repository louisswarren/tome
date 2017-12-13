open import common

module formula where


--------------------------------------------------------------------------------
-- Relation symbols
--------------------------------------------------------------------------------

data _-aryRelationSymbol : ℕ → Set where
  _-aryrelationsymbol_ : (n : ℕ) → String → (n)-aryRelationSymbol

-- Special case: propositional symbols
Propsymbol = (zero)-aryRelationSymbol
propsymbol : String → Propsymbol
propsymbol s = (zero)-aryrelationsymbol s


--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

data _-aryFunctionSymbol : ℕ → Set where
  _-aryfunctionsymbol_ : (n : ℕ) → String → (n)-aryFunctionSymbol

-- Special case: constant symbols
ConstantSymbol = (zero)-aryFunctionSymbol
constantsymbol : String → ConstantSymbol
constantsymbol s = (zero)-aryfunctionsymbol s


data Variable : Set where
  variable : String → Variable


data Term : Set where
  variableterm : Variable → Term
  functionterm : ∀{n} → (n)-aryFunctionSymbol → Vector Term n → Term

-- Special case: terms from constant symbols
constantterm : ConstantSymbol → Term
constantterm t = functionterm t []


--------------------------------------------------------------------------------
-- Formulae
--------------------------------------------------------------------------------

data Formula : Set where
  atomic      : ∀{n} → (n)-aryRelationSymbol → Vector Term n → Formula
  _⇒_         : Formula → Formula → Formula
  _∧_         : Formula → Formula → Formula
  _∨_         : Formula → Formula → Formula
  universal   : Variable → Formula → Formula
  existential : Variable → Formula → Formula

infixr 110 _∨_
infixr 120 _∧_
infixr 130 _⇒_


--------------------------------------------------------------------------------
-- Relations and functions
--------------------------------------------------------------------------------

-- Idea: A predicate (1-ary relation) symbol called "P" is just an element in
-- the language.
--     P-symbol : (1)-aryRelationSymbol
--     P-symbol = (1)-aryrelationsymbol "P"
-- To be able to use it here inside formulae, we create a predicate so that
-- (P x) gives the appropriate atomic formula.
--     P : Term → Formula
--     P x = atomic (P-symbol) (x ∷ [])

Proposition = Formula
proposition : String → Proposition
proposition s = (atomic (propsymbol s) ([]))

Predicate = Term → Formula
predicate : String → Predicate
predicate s = λ σ → (atomic ((1)-aryrelationsymbol s) (σ ∷ []))

BinaryRelation = Term → Term → Formula
binaryrelation : String → BinaryRelation
binaryrelation s = λ σ τ → (atomic ((2)-aryrelationsymbol s) (σ ∷ τ ∷ []))


Constant = Term
constant : String → Constant
constant s = constantterm (constantsymbol s)

UnaryFunction = Term → Term
unaryfunction : String → UnaryFunction
unaryfunction s = λ n → (functionterm ((1)-aryfunctionsymbol s) (n ∷ []))

BinaryFunction = Term → Term → Term
binaryfunction : String → BinaryFunction
binaryfunction s = λ n m → (functionterm ((2)-aryfunctionsymbol s) (n ∷ m ∷ []))


--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

x : Term
x = variableterm (variable "x")

∀x ∃x : Formula → Formula
∀x = universal   (variable "x")
∃x = existential (variable "x")


y : Term
y = variableterm (variable "y")

∀y ∃y : Formula → Formula
∀y = universal   (variable "y")
∃y = existential (variable "y")

s t : Term
s = constant "s"
t = constant "t"

f : BinaryFunction
f = binaryfunction "f"

P : Predicate
P = predicate "P"

Q : Proposition
Q = proposition "Q"

R : BinaryRelation
R = binaryrelation "R"

α : Formula
α = ∀x (P x) ∨ ∃y (∀x (R x t) ⇒ Q) ∧ (P (f t y) ∨ (R x x))

