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


⊥ = proposition "⊥"
¬ : Formula → Formula
¬ α = α ⇒ ⊥


--------------------------------------------------------------------------------
-- Equality
--------------------------------------------------------------------------------

_=variable=_ : Variable → Variable → Bool
variable x =variable= variable y = x === y

_=functionsymbol=_ : ∀{n m}
                     → (n)-aryFunctionSymbol
                     → (m)-aryFunctionSymbol
                     → Bool
(n -aryfunctionsymbol x) =functionsymbol= (m -aryfunctionsymbol y)
  = (n == m) and (x === y)

_=vectorterm=_ : ∀{n m} → Vector Term n → Vector Term m → Bool

_=term=_ : Term → Term → Bool
variableterm x    =term= variableterm y   = x =variable= y
variableterm _    =term= functionterm _ _ = false
functionterm _ _  =term= variableterm _   = false
functionterm f ζ =term= functionterm g χ
  = (f =functionsymbol= g) and (ζ =vectorterm= χ)

[] =vectorterm= [] = true
(z ∷ ζ) =vectorterm= (x ∷ χ) = (x =term= z) and (ζ =vectorterm= χ)
_ =vectorterm= _ = false

substituteone : Term → Term → Term → Term

substitute : ∀{n} → Vector Term n → Term → Term → Vector Term n
substitute [] σ τ = []
substitute (ζ ∷ ζs) σ τ = {! (substituteone ζ σ τ) ∷ (substitute ζs σ τ)  !}

substituteone ζ σ τ with (ζ =term= σ)
...               | true = τ
...               | false with ζ
...                     | variableterm x = ζ
...                     | functionterm x xs = functionterm x (substitute xs σ τ)

--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

_[_/_] : Formula → Term → Term → Formula
atomic r ζs [ σ / τ ]     = atomic r (substitute ζs σ τ)
(α ⇒ β) [ σ / τ ]         = (α [ σ / τ ]) ⇒ (β [ σ / τ ])
(α ∧ β) [ σ / τ ]         = (α [ σ / τ ]) ∧ (β [ σ / τ ])
(α ∨ β) [ σ / τ ]         = (α [ σ / τ ]) ∨ (β [ σ / τ ])
universal ζ α [ σ@(variableterm x) / τ ] with (ζ =variable= x)
...                                      | true = universal ζ α
...                                      | false = universal ζ (α [ σ / τ ])
universal ζ α [ σ@(functionterm _ _) / τ ] = universal ζ (α [ σ / τ ])
existential ζ α [ σ@(variableterm x) / τ ] with (ζ =variable= x)
...                                      | true = existential ζ α
...                                      | false = existential ζ (α [ σ / τ ])
existential ζ α [ σ@(functionterm _ _) / τ ] = existential ζ (α [ σ / τ ])

