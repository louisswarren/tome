module Formula where

open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Decidable
open import Nat
open import Vec


-- "Let a countably infinite set {vi | i ∈ N} of variables be given."
record Variable : Set where
  constructor var
  field
    idx : ℕ

open Variable renaming (idx to varidx)

-- "For every natural number n ≥ 0 a ... set of n-ary function symbols."
record Function : Set where
  constructor func
  field
    idx   : ℕ
    arity : ℕ

open Function renaming (idx to funcidx ; arity to funcarity)

-- "Terms are inductively defined as follows.
--  (i)   Every variable is a term.
--  (ii)  Every constant is a term.
--  (iii) If t1, . . . , tn are terms and f is an n-ary function symbol with
--        n ≥ 1, then f(t1 , . . . , tn ) is a term."
data Term : Set where
  varterm  : (x : Variable) → Term
  functerm : (f : Function) → (ts : Vec Term (funcarity f)) → Term


-- "For every natural number n ≥ 0 a ... set of n-ary relation symbols."
record Relation : Set where
  constructor rel
  field
    idx   : ℕ
    arity : ℕ

open Relation renaming (idx to relidx ; arity to relarity)

-- "If t1, . . . , tn are terms and R is an n-ary relation symbol, then
--  R(t1, . . . , tn ) is a prime formula ... Formulas are inductively defined
--  from prime formulas."
data Formula : Set where
  atom   : (r : Relation) → (ts : Vec Term (relarity r)) → Formula
  _⇒_    : (α : Formula)  → (β : Formula) → Formula
  _∧_    : (α : Formula)  → (β : Formula) → Formula
  _∨_    : (α : Formula)  → (β : Formula) → Formula
  Λ      : (x : Variable) → (α : Formula) → Formula
  V      : (x : Variable) → (α : Formula) → Formula

_⇔_ : Formula → Formula → Formula
Φ ⇔ Ψ = (Φ ⇒ Ψ) ∧ (Ψ ⇒ Φ)

infixr 105 _⇒_ _⇔_
infixr 106 _∨_
infixr 107 _∧_


record Scheme : Set where
  constructor scheme
  field
    idx   : String
    arity : ℕ
    inst  : Vec Formula arity → Formula


-- Variable freedom

infix 300 _NotFreeInTerm_ _NotFreeInTerms_ _NotFreeIn_ [_][_/_]≡_ _[_/_]≡_

data _NotFreeInTerm_ (x : Variable) : Term → Set

_NotFreeInTerms_ : ∀{n} → Variable → Vec Term n → Set
x NotFreeInTerms ts = All (x NotFreeInTerm_) ts

data _NotFreeInTerm_ x where
  varterm  : ∀{y} → x ≢ y → x NotFreeInTerm (varterm y)
  functerm : ∀{f} {us : Vec Term (funcarity f)}
               → x NotFreeInTerms us → x NotFreeInTerm (functerm f us)

data _NotFreeIn_ : Variable → Formula → Set where
  atom : ∀{x r} {ts : Vec Term (relarity r)}
                  → x NotFreeInTerms ts → x NotFreeIn (atom r ts)
  _⇒_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ⇒ β)
  _∧_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ∧ β)
  _∨_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ∨ β)
  Λ∣   : ∀ x α    → x NotFreeIn Λ x α
  V∣   : ∀ x α    → x NotFreeIn V x α
  Λ    : ∀{x α}   → ∀ y → x NotFreeIn α → x NotFreeIn Λ y α
  V    : ∀{x α}   → ∀ y → x NotFreeIn α → x NotFreeIn V y α


-- Variable substitution

data [_][_/_]≡_ : ∀{n} → Vec Term n → Variable → Term → Vec Term n → Set

data ⟨_⟩[_/_]≡_ : Term → Variable → Term → Term → Set where
  varterm≡ : ∀{x t} → ⟨ varterm x ⟩[ x / t ]≡ t
  varterm≢ : ∀{x t y} → x ≢ y → ⟨ varterm y ⟩[ x / t ]≡ varterm y
  functerm : ∀{x t f us vs} → [ us ][ x  / t ]≡ vs
               → ⟨ functerm f us ⟩[ x / t ]≡ functerm f vs

data [_][_/_]≡_ where
  []  : ∀{x t} → [ [] ][ x / t ]≡ []
  _∷_ : ∀{x t u v n} {us vs : Vec Term n}
        → ⟨ u ⟩[ x / t ]≡ v → [ us ][ x / t ]≡ vs
        → [ u ∷ us ][ x / t ]≡ (v ∷ vs)

data _[_/_]≡_ : Formula → Variable → Term → Formula → Set where
  ident : ∀ α x → α [ x / varterm x ]≡ α
  notfree : ∀{α x t} → x NotFreeIn α → α [ x / t ]≡ α
  atom    : ∀{x t}
              → (r : Relation) → {xs ys : Vec Term (relarity r)}
              → [ xs ][ x / t ]≡ ys → (atom r xs) [ x / t ]≡ (atom r ys)
  _⇒_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ⇒ β) [ x / t ]≡ (α′ ⇒ β′)
  _∧_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∧ β) [ x / t ]≡ (α′ ∧ β′)
  _∨_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∨ β) [ x / t ]≡ (α′ ∨ β′)
  Λ∣      : ∀{t} → (x : Variable) → (α : Formula) → (Λ x α) [ x / t ]≡ (Λ x α)
  V∣      : ∀{t} → (x : Variable) → (α : Formula) → (V x α) [ x / t ]≡ (V x α)
  Λ       : ∀{α β x y t} → x ≢ y → y NotFreeInTerm t
              → α [ x / t ]≡ β → (Λ y α) [ x / t ]≡ (Λ y β)
  V       : ∀{α β x y t} → x ≢ y → y NotFreeInTerm t
              → α [ x / t ]≡ β → (V y α) [ x / t ]≡ (V y β)


data _FreeFor_In_ (t : Term) (x : Variable) : Formula → Set where
  notfree : ∀{α} → x NotFreeIn α → t FreeFor x In α
  atom    : ∀ r us → t FreeFor x In atom r us
  _⇒_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ⇒ β
  _∧_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ∧ β
  _∨_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ∨ β
  Λ∣      : ∀ α → t FreeFor x In Λ x α
  V∣      : ∀ α → t FreeFor x In V x α
  Λ       : ∀ α y → y NotFreeInTerm t → t FreeFor x In α → t FreeFor x In Λ y α
  V       : ∀ α y → y NotFreeInTerm t → t FreeFor x In α → t FreeFor x In V y α


data _FreshIn_ (x : Variable) : Formula → Set where
  atom : ∀{r ts} → x NotFreeInTerms ts  → x FreshIn (atom r ts)
  _⇒_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ⇒ β
  _∧_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ∧ β
  _∨_  : ∀{α β} → x FreshIn α → x FreshIn β → x FreshIn α ∨ β
  Λ    : ∀{α y} → x ≢ y → x FreshIn α → x FreshIn Λ y α
  V    : ∀{α y} → x ≢ y → x FreshIn α → x FreshIn V y α


--------------------------------------------------------------------------------
-- Computation requires decidable equality for the types above

natEq : Decidable≡ ℕ
natEq zero zero = yes refl
natEq zero (suc m) = no λ ()
natEq (suc n) zero = no λ ()
natEq (suc n) (suc m) with natEq n m
...                   | yes refl = yes refl
...                   | no  n≢m  = no λ { refl → n≢m refl }

varEq : Decidable≡ Variable
varEq (var n) (var m) with natEq n m
...                   | yes refl = yes refl
...                   | no  n≢m  = no λ { refl → n≢m refl }

relEq : Decidable≡ Relation
relEq (rel n j) (rel m k) with natEq n m
...                       | no  n≢m  = no λ { refl → n≢m refl }
...                       | yes refl with natEq j k
...                                  | yes refl = yes refl
...                                  | no  j≢k  = no λ { refl → j≢k refl }

funcEq : Decidable≡ Function
funcEq (func n j) (func m k) with natEq n m
...                          | no  n≢m  = no λ { refl → n≢m refl }
...                          | yes refl with natEq j k
...                                     | yes refl = yes refl
...                                     | no  j≢k  = no λ { refl → j≢k refl }

vecEq : ∀{n} {A : Set} → Decidable≡ A → Decidable≡ (Vec A n)
vecEq eq [] [] = yes refl
vecEq eq (x ∷ xs) (y ∷ ys) with eq x y
...                        | no  x≢y  = no λ { refl → x≢y refl }
...                        | yes refl with vecEq eq xs ys
...                                   | yes refl  = yes refl
...                                   | no  xs≢xy = no λ { refl → xs≢xy refl }

termEq : Decidable≡ Term
termEq (varterm x)     (varterm y)     with varEq x y
...                                    | yes refl = yes refl
...                                    | no  x≢y  = no λ { refl → x≢y refl }
termEq (varterm x)     (functerm f ts) = no λ ()
termEq (functerm f ts) (varterm x)     = no λ ()
termEq (functerm f []) (functerm g []) with funcEq f g
...                                    | yes refl = yes refl
...                                    | no  f≢g  = no λ { refl → f≢g refl }
termEq (functerm f []) (functerm g (_ ∷ _)) = no λ ()
termEq (functerm f (_ ∷ _)) (functerm g []) = no λ ()
termEq
  (functerm (func n (suc j)) (u ∷ us)) (functerm (func m (suc k)) (v ∷ vs))
  with natEq j k
... | no  j≢k  = no λ { refl → j≢k refl }
... | yes refl with termEq u v
...   | no  u≢v  = no λ { refl → u≢v refl }
...   | yes refl
        with termEq (functerm (func n j) us) (functerm (func m k) vs)
...     | yes refl = yes refl
...     | no  neq  = no λ { refl → neq refl }

formulaEq : Decidable≡ Formula
formulaEq (atom r xs) (atom s ys)
    with natEq (relarity r) (relarity s)
... | no ar≢as = no λ { refl → ar≢as refl }
... | yes refl with (relEq r s) | (vecEq termEq xs ys)
...            | yes refl | yes refl  = yes refl
...            | _        | no  xs≢ys = no λ { refl → xs≢ys refl }
...            | no  r≢s  | _         = no λ { refl → r≢s refl }
formulaEq (α ⇒ β) (γ ⇒ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  β≢δ  = no λ { refl → β≢δ refl }
...                       | no  α≢γ  | _        = no λ { refl → α≢γ refl }
formulaEq (α ∧ β) (γ ∧ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  β≢δ  = no λ { refl → β≢δ refl }
...                       | no  α≢γ  | _        = no λ { refl → α≢γ refl }
formulaEq (α ∨ β) (γ ∨ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  β≢δ  = no λ { refl → β≢δ refl }
...                       | no  α≢γ  | _        = no λ { refl → α≢γ refl }
formulaEq (Λ x α) (Λ y β) with (varEq x y) | (formulaEq α β)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  α≢β  = no λ { refl → α≢β refl }
...                       | no  x≢y  | _        = no λ { refl → x≢y refl }
formulaEq (V x α) (V y β) with (varEq x y) | (formulaEq α β)
...                       | yes refl | yes refl = yes refl
...                       | _        | no  α≢β  = no λ { refl → α≢β refl }
...                       | no  x≢y  | _        = no λ { refl → x≢y refl }
formulaEq (atom r us) (γ ⇒ δ)     = no λ ()
formulaEq (atom r us) (γ ∧ δ)     = no λ ()
formulaEq (atom r us) (γ ∨ δ)     = no λ ()
formulaEq (atom r us) (Λ y γ)     = no λ ()
formulaEq (atom r us) (V y γ)     = no λ ()
formulaEq (α ⇒ β)     (atom r vs) = no λ ()
formulaEq (α ⇒ β)     (γ ∧ δ)     = no λ ()
formulaEq (α ⇒ β)     (γ ∨ δ)     = no λ ()
formulaEq (α ⇒ β)     (Λ y γ)     = no λ ()
formulaEq (α ⇒ β)     (V y γ)     = no λ ()
formulaEq (α ∧ β)     (atom r vs) = no λ ()
formulaEq (α ∧ β)     (γ ⇒ δ)     = no λ ()
formulaEq (α ∧ β)     (γ ∨ δ)     = no λ ()
formulaEq (α ∧ β)     (Λ y γ)     = no λ ()
formulaEq (α ∧ β)     (V y γ)     = no λ ()
formulaEq (α ∨ β)     (atom r vs) = no λ ()
formulaEq (α ∨ β)     (γ ⇒ δ)     = no λ ()
formulaEq (α ∨ β)     (γ ∧ δ)     = no λ ()
formulaEq (α ∨ β)     (Λ y γ)     = no λ ()
formulaEq (α ∨ β)     (V y γ)     = no λ ()
formulaEq (Λ x α)     (atom r vs) = no λ ()
formulaEq (Λ x α)     (γ ⇒ δ)     = no λ ()
formulaEq (Λ x α)     (γ ∧ δ)     = no λ ()
formulaEq (Λ x α)     (γ ∨ δ)     = no λ ()
formulaEq (Λ x α)     (V y γ)     = no λ ()
formulaEq (V x α)     (atom r vs) = no λ ()
formulaEq (V x α)     (γ ⇒ δ)     = no λ ()
formulaEq (V x α)     (γ ∧ δ)     = no λ ()
formulaEq (V x α)     (γ ∨ δ)     = no λ ()
formulaEq (V x α)     (Λ y γ)     = no λ ()


--------------------------------------------------------------------------------

-- Decidablity proofs

_notFreeInTerms_ : ∀{n} → (x : Variable) → (ts : Vec Term n)
                   → Dec (x NotFreeInTerms ts)
x notFreeInTerms [] = yes []
x notFreeInTerms (varterm y ∷ ts) with varEq x y
... | yes refl = no λ { (varterm nrefl ∷ _) → nrefl refl }
... | no x≢y   with x notFreeInTerms ts
...            | yes xnfts = yes (varterm x≢y ∷ xnfts)
...            | no xfts   = no λ { (_ ∷ xnfts) → xfts xnfts }
x notFreeInTerms (functerm f us ∷ ts) with x notFreeInTerms us
... | no xfus   = no λ { (functerm xnfus ∷ _) → xfus xnfus }
... | yes xnfus with x notFreeInTerms ts
...             | yes xnfts = yes (functerm xnfus ∷ xnfts)
...             | no xfts   = no λ { (_ ∷ xnfts) → xfts xnfts }


_notFreeInTerm_ : (x : Variable) → (t : Term) → Dec (x NotFreeInTerm t)
x notFreeInTerm t with x notFreeInTerms (t ∷ [])
x notFreeInTerm t | yes (pf ∷ []) = yes pf
x notFreeInTerm t | no npf        = no λ z → npf (z ∷ [])


_notFreeIn_ : (x : Variable) → (α : Formula) → Dec (x NotFreeIn α)
x notFreeIn atom r ts with x notFreeInTerms ts
x notFreeIn atom r ts | yes bdts = yes (atom bdts)
x notFreeIn atom r ts | no ¬bdts = no λ { (atom bdts) → ¬bdts bdts }
x notFreeIn (α ⇒ β)   with x notFreeIn α | x notFreeIn β
x notFreeIn (α ⇒ β)   | yes αbd | yes βbd = yes (αbd ⇒ βbd)
x notFreeIn (α ⇒ β)   | _       | no ¬βbd = no λ { (αbd ⇒ βbd) → ¬βbd βbd }
x notFreeIn (α ⇒ β)   | no ¬αbd | _       = no λ { (αbd ⇒ βbd) → ¬αbd αbd }
x notFreeIn (α ∧ β)   with x notFreeIn α | x notFreeIn β
x notFreeIn (α ∧ β)   | yes αbd | yes βbd = yes (αbd ∧ βbd)
x notFreeIn (α ∧ β)   | _       | no ¬βbd = no λ { (αbd ∧ βbd) → ¬βbd βbd }
x notFreeIn (α ∧ β)   | no ¬αbd | _       = no λ { (αbd ∧ βbd) → ¬αbd αbd }
x notFreeIn (α ∨ β)   with x notFreeIn α | x notFreeIn β
x notFreeIn (α ∨ β)   | yes αbd | yes βbd = yes (αbd ∨ βbd)
x notFreeIn (α ∨ β)   | _       | no ¬βbd = no λ { (αbd ∨ βbd) → ¬βbd βbd }
x notFreeIn (α ∨ β)   | no ¬αbd | _       = no λ { (αbd ∨ βbd) → ¬αbd αbd }
x notFreeIn Λ  y α    with varEq x y
x notFreeIn Λ .x α    | yes refl = yes (Λ∣ x α)
x notFreeIn Λ  y α    | no x≢y with x notFreeIn α
x notFreeIn Λ  y α    | no x≢y | yes αbd = yes (Λ y αbd)
x notFreeIn Λ  y α    | no x≢y | no ¬αbd = no λ { (Λ∣ x α)  → x≢y refl
                                                ; (Λ y αbd) → ¬αbd αbd }
x notFreeIn V  y α    with varEq x y
x notFreeIn V .x α    | yes refl = yes (V∣ x α)
x notFreeIn V  y α    | no x≢y with x notFreeIn α
x notFreeIn V  y α    | no x≢y | yes αbd = yes (V y αbd)
x notFreeIn V  y α    | no x≢y | no ¬αbd = no λ { (V∣ x α)  → x≢y refl
                                                ; (V y αbd) → ¬αbd αbd }

-- Generating not-free variables
supFreeTerms : ∀{k} → (ts : Vec Term k) → Σ ℕ λ ⌈ts⌉ → ∀ n → ⌈ts⌉ < n
               → var n NotFreeInTerms ts
supFreeTerms [] = zero , λ _ _ → []
supFreeTerms (varterm (var m) ∷ ts) with supFreeTerms ts
... | ⌈ts⌉ , tspf with max m ⌈ts⌉
...               | less m≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    orderneq : ∀{n m} → n < m → var m ≢ var n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n
                    → All (var n NotFreeInTerm_) (varterm (var m) ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = varterm (orderneq (≤trans (sn≤sm m≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
...               | more ⌈ts⌉≤m = m , notFreeIsm
  where
    orderneq : ∀{n m} → n < m → var m ≢ var n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIsm : ∀ n → m < n
                 → All (var n NotFreeInTerm_) (varterm (var m) ∷ ts)
    notFreeIsm n m<n = varterm (orderneq m<n)
                       ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤m) m<n)
supFreeTerms (functerm f us     ∷ ts) with supFreeTerms us | supFreeTerms ts
... | ⌈us⌉ , uspf | ⌈ts⌉ , tspf with max ⌈us⌉ ⌈ts⌉
...                             | less ⌈us⌉≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n
                    → All (var n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = functerm (uspf n (≤trans (sn≤sm ⌈us⌉≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
...                             | more ⌈ts⌉≤⌈us⌉ = ⌈us⌉ , notFreeIs⌈us⌉
  where
    notFreeIs⌈us⌉ : ∀ n → ⌈us⌉ < n
                    → All (var n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈us⌉ n ⌈us⌉<n = functerm (uspf n ⌈us⌉<n)
                             ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤⌈us⌉) ⌈us⌉<n)


minFresh : ∀ α → Σ Variable λ ⌈α⌉ → ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn α
minFresh (atom r ts) with supFreeTerms ts
minFresh (atom r ts) | ⌈ts⌉ , tspf = var (suc ⌈ts⌉)
                                     , (λ n ⌈ts⌉≤n → atom (tspf n ⌈ts⌉≤n))
minFresh (α ⇒ β) with minFresh α | minFresh β
...              | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max (varidx ⌈α⌉) (varidx ⌈β⌉)
...                                      | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , freshIs⌈β⌉
  where
    freshIs⌈β⌉ : ∀ n → varidx ⌈β⌉ ≤ n → var n FreshIn (α ⇒ β)
    freshIs⌈β⌉ n ⌈β⌉≤n = αpf n (≤trans ⌈α⌉≤⌈β⌉ ⌈β⌉≤n) ⇒ βpf n ⌈β⌉≤n
...                                      | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn (α ⇒ β)
    freshIs⌈α⌉ n ⌈α⌉≤n = αpf n ⌈α⌉≤n ⇒ βpf n (≤trans ⌈β⌉≤⌈α⌉ ⌈α⌉≤n)
minFresh (α ∧ β) with minFresh α | minFresh β
...              | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max (varidx ⌈α⌉) (varidx ⌈β⌉)
...                                      | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , freshIs⌈β⌉
  where
    freshIs⌈β⌉ : ∀ n → varidx ⌈β⌉ ≤ n → var n FreshIn (α ∧ β)
    freshIs⌈β⌉ n ⌈β⌉≤n = αpf n (≤trans ⌈α⌉≤⌈β⌉ ⌈β⌉≤n) ∧ βpf n ⌈β⌉≤n
...                                      | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn (α ∧ β)
    freshIs⌈α⌉ n ⌈α⌉≤n = αpf n ⌈α⌉≤n ∧ βpf n (≤trans ⌈β⌉≤⌈α⌉ ⌈α⌉≤n)
minFresh (α ∨ β) with minFresh α | minFresh β
...              | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max (varidx ⌈α⌉) (varidx ⌈β⌉)
...                                      | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , freshIs⌈β⌉
  where
    freshIs⌈β⌉ : ∀ n → varidx ⌈β⌉ ≤ n → var n FreshIn (α ∨ β)
    freshIs⌈β⌉ n ⌈β⌉≤n = αpf n (≤trans ⌈α⌉≤⌈β⌉ ⌈β⌉≤n) ∨ βpf n ⌈β⌉≤n
...                                      | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn (α ∨ β)
    freshIs⌈α⌉ n ⌈α⌉≤n = αpf n ⌈α⌉≤n ∨ βpf n (≤trans ⌈β⌉≤⌈α⌉ ⌈α⌉≤n)
minFresh (Λ x@(var k) α) with minFresh α
...                      | ⌈α⌉ , αpf with max (suc k) (varidx ⌈α⌉)
...                                  | less sk≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var n ≢ var m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn Λ x α
    freshIs⌈α⌉ n ⌈α⌉≤n = Λ (skNewLemma (≤trans sk≤⌈α⌉ ⌈α⌉≤n)) (αpf n ⌈α⌉≤n)
...                                  | more ⌈α⌉≤sk = var (suc k) , freshIssk
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var n ≢ var m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIssk : ∀ n → suc k ≤ n → var n FreshIn Λ x α
    freshIssk n sk≤n = Λ (skNewLemma sk≤n) (αpf n (≤trans ⌈α⌉≤sk sk≤n))
minFresh (V x@(var k) α) with minFresh α
...                      | ⌈α⌉ , αpf with max (suc k) (varidx ⌈α⌉)
...                                  | less sk≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var n ≢ var m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIs⌈α⌉ : ∀ n → varidx ⌈α⌉ ≤ n → var n FreshIn V x α
    freshIs⌈α⌉ n ⌈α⌉≤n = V (skNewLemma (≤trans sk≤⌈α⌉ ⌈α⌉≤n)) (αpf n ⌈α⌉≤n)
...                                    | more ⌈α⌉≤sk = var (suc k) , freshIssk
  where
    skNewLemma : ∀{n m} → suc m ≤ n → var n ≢ var m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIssk : ∀ n → suc k ≤ n → var n FreshIn V x α
    freshIssk n sk≤n = V (skNewLemma sk≤n) (αpf n (≤trans ⌈α⌉≤sk sk≤n))

fresh : ∀ α → Σ Variable (_FreshIn α)
fresh α with minFresh α
...     | ⌈α⌉ , αpf = ⌈α⌉ , αpf (varidx ⌈α⌉) ≤refl

-- Computing replacements

[_][_/_] : ∀{n} → (us : Vec Term n) → ∀ x t → Σ (Vec Term n) λ vs
           → [ us ][ x / t ]≡ vs
[ [] ][ x / t ] = [] , []
[ varterm y ∷ us ][ x / t ] with [ us ][ x / t ]
... | vs , [us][x/t]≡vs with varEq x y
...   | yes refl = (t ∷ vs) , (varterm≡ ∷ [us][x/t]≡vs)
...   | no x≢y   = (varterm y ∷ vs) , (varterm≢ x≢y ∷ [us][x/t]≡vs)
[ functerm f ws ∷ us ][ x / t ] with [ us ][ x / t ]
... | vs , [us][x/t]≡vs with [ ws ][ x / t ]
...   | xs , [ws][x/t]≡xs = (functerm f xs ∷ vs)
                            , (functerm [ws][x/t]≡xs ∷ [us][x/t]≡vs)


_[_/_] : ∀{t} → ∀ α x → t FreeFor x In α → Σ Formula (α [ x / t ]≡_)
α [ x / notfree xnfα ]          = α , notfree xnfα
_[_/_] {t} (atom r ts) x tff    with [ ts ][ x / t ]
_[_/_] {t} (atom r ts) x tff    | ts′ , tspf = atom r ts′ , atom r tspf
(α ⇒ β) [ x / tffα ⇒ tffβ ]     with α [ x / tffα ] | β [ x / tffβ ]
...                             | α′ , αpf | β′ , βpf = α′ ⇒ β′ , αpf ⇒ βpf
(α ∧ β) [ x / tffα ∧ tffβ ]     with α [ x / tffα ] | β [ x / tffβ ]
...                             | α′ , αpf | β′ , βpf = α′ ∧ β′ , αpf ∧ βpf
(α ∨ β) [ x / tffα ∨ tffβ ]     with α [ x / tffα ] | β [ x / tffβ ]
...                             | α′ , αpf | β′ , βpf = α′ ∨ β′ , αpf ∨ βpf
Λ y α [ .y / Λ∣ .α ]            = Λ y α , Λ∣ y α
Λ y α [ x / Λ .α .y ynft tffα ] with varEq x y
...                             | yes refl = Λ y α , Λ∣ y α
...                             | no  x≢y  with α [ x / tffα ]
...                                        | α′ , αpf = Λ y α′ , Λ x≢y ynft αpf
V y α [ .y / V∣ .α ]            = V y α , V∣ y α
V y α [ x / V .α .y ynft tffα ] with varEq x y
...                             | yes refl = V y α , V∣ y α
...                             | no  x≢y  with α [ x / tffα ]
...                                        | α′ , αpf = V y α′ , V x≢y ynft αpf


-- Some useful lemata

subNotFree : ∀{α x t β} → x NotFreeInTerm t → α [ x / t ]≡ β → x NotFreeIn β
subNotFree (varterm x≢x) (ident α x) = ⊥-elim (x≢x refl)
subNotFree xnft (notfree xnfα)   = xnfα
subNotFree xnft (atom r p)       = atom (termsLemma xnft p)
  where
    termsLemma : ∀{n x t} {us vs : Vec Term n} → x NotFreeInTerm t
                      → [ us ][ x / t ]≡ vs → x NotFreeInTerms vs
    termsLemma xnft []                  = []
    termsLemma xnft (varterm≡ ∷ ps)     = xnft ∷ termsLemma xnft ps
    termsLemma xnft (varterm≢ neq ∷ ps) = varterm neq ∷ termsLemma xnft ps
    termsLemma xnft (functerm sub ∷ ps) = functerm (termsLemma xnft sub)
                                           ∷ termsLemma xnft ps
subNotFree xnft (pα ⇒ pβ)        = subNotFree xnft pα ⇒ subNotFree xnft pβ
subNotFree xnft (pα ∧ pβ)        = subNotFree xnft pα ∧ subNotFree xnft pβ
subNotFree xnft (pα ∨ pβ)        = subNotFree xnft pα ∨ subNotFree xnft pβ
subNotFree xnft (Λ∣ y α)         = Λ∣ y α
subNotFree xnft (Λ x≢y ynft p)   = Λ _ (subNotFree xnft p)
subNotFree xnft (V∣ y α)         = V∣ y α
subNotFree xnft (V x≢y ynft p)   = V _ (subNotFree xnft p)


freshNotFree : ∀{α x} → x FreshIn α → x NotFreeIn α
freshNotFree (atom xnfts)  = atom xnfts
freshNotFree (xfrα ⇒ xfrβ) = freshNotFree xfrα ⇒ freshNotFree xfrβ
freshNotFree (xfrα ∧ xfrβ) = freshNotFree xfrα ∧ freshNotFree xfrβ
freshNotFree (xfrα ∨ xfrβ) = freshNotFree xfrα ∨ freshNotFree xfrβ
freshNotFree (Λ _ xfrα)    = Λ _ (freshNotFree xfrα)
freshNotFree (V _ xfrα)    = V _ (freshNotFree xfrα)


freshFreeFor : ∀{α x y} → x FreshIn α → (varterm x) FreeFor y In α
freshFreeFor (atom _)      = atom _ _
freshFreeFor (xfrα ⇒ xfrβ) = freshFreeFor xfrα ⇒ freshFreeFor xfrβ
freshFreeFor (xfrα ∧ xfrβ) = freshFreeFor xfrα ∧ freshFreeFor xfrβ
freshFreeFor (xfrα ∨ xfrβ) = freshFreeFor xfrα ∨ freshFreeFor xfrβ
freshFreeFor (Λ x≢y xfrα)  = Λ _ _
                             (varterm λ { refl → x≢y refl }) (freshFreeFor xfrα)
freshFreeFor (V x≢y xfrα)  = V _ _
                             (varterm λ { refl → x≢y refl }) (freshFreeFor xfrα)


subInverse : ∀{ω α x β}
             → ω NotFreeIn α → α [ x / varterm ω ]≡ β → β [ ω / varterm x ]≡ α
subInverse _            (ident α x)    = ident α x
subInverse ωnfα         (notfree xnf)  = notfree ωnfα
subInverse (atom xnfts) (atom r repts) = atom r (termsLemma xnfts repts)
  where
    termsLemma : ∀{n x ω} {us vs : Vec Term n} → ω NotFreeInTerms us
                 → [ us ][ x / varterm ω ]≡ vs → [ vs ][ ω / varterm x ]≡ us
    termsLemma ωnfus [] = []
    termsLemma (_ ∷ ωnfus) (varterm≡ ∷ repus) = varterm≡ ∷ termsLemma ωnfus repus
    termsLemma (varterm ω≢y ∷ ωnfus) (varterm≢ x≢ω ∷ repus) = varterm≢ ω≢y ∷ termsLemma ωnfus repus
    termsLemma (functerm ωnfts ∷ ωnfus) (functerm repts ∷ repus) = functerm (termsLemma ωnfts repts) ∷ termsLemma ωnfus repus
subInverse (ωnfα ⇒ ωnfβ) (repα ⇒ repβ) = subInverse ωnfα repα ⇒ subInverse ωnfβ repβ
subInverse (ωnfα ∧ ωnfβ) (repα ∧ repβ) = subInverse ωnfα repα ∧ subInverse ωnfβ repβ
subInverse (ωnfα ∨ ωnfβ) (repα ∨ repβ) = subInverse ωnfα repα ∨ subInverse ωnfβ repβ
subInverse ωnfα          (Λ∣ x α)              = notfree ωnfα
subInverse (Λ∣ x α)      (Λ _ (varterm x≢x) _) = ⊥-elim (x≢x refl)
subInverse ωnfα          (V∣ x α)              = notfree ωnfα
subInverse (V∣ x α)      (V _ (varterm x≢x) _) = ⊥-elim (x≢x refl)
subInverse {ω} (Λ y ωnfα) (Λ x≢y ynfω repα)           with varEq ω y
subInverse {ω} (Λ y ωnfα) (Λ x≢y ynfω repα)           | no ω≢y = Λ ω≢y (varterm λ { refl → x≢y refl }) (subInverse ωnfα repα)
subInverse {.y} (Λ y ωnfα) (Λ x≢y (varterm y≢y) repα) | yes refl = ⊥-elim (y≢y refl)
subInverse {ω} (V y ωnfα) (V x≢y ynfω repα)           with varEq ω y
subInverse {.y} (V y ωnfα) (V x≢y (varterm y≢y) repα) | yes refl = ⊥-elim (y≢y refl)
subInverse {ω} (V y ωnfα) (V x≢y ynfω repα)           | no ω≢y = V ω≢y (varterm λ { refl → x≢y refl }) (subInverse ωnfα repα)
