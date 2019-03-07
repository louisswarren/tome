module Formula where

open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Decidable
open import Nat
open import Vec


-- "Let a countably infinite set {vi | i ∈ N} of variables be given."
record Variable : Set where
  constructor mkvar
  field
    idx : ℕ


-- "For every natural number n ≥ 0 a ... set of n-ary function symbols."
record Function : Set where
  constructor mkfunc
  field
    idx   : ℕ
    arity : ℕ


-- "Terms are inductively defined as follows.
--  (i)   Every variable is a term.
--  (ii)  Every constant is a term.
--  (iii) If t1, . . . , tn are terms and f is an n-ary function symbol with
--        n ≥ 1, then f(t1 , . . . , tn ) is a term."
data Term : Set where
  varterm  : (x : Variable) → Term
  functerm : (f : Function) → (ts : Vec Term (Function.arity f)) → Term


-- "For every natural number n ≥ 0 a ... set of n-ary relation symbols."
record Relation : Set where
  constructor mkrel
  field
    idx   : ℕ
    arity : ℕ


-- "If t1, . . . , tn are terms and R is an n-ary relation symbol, then
--  R(t1, . . . , tn ) is a prime formula ... Formulas are inductively defined
--  from prime formulas."
data Formula : Set where
  atom   : (r : Relation) → (ts : Vec Term (Relation.arity r)) → Formula
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
  functerm : ∀{f} {us : Vec Term (Function.arity f)}
               → x NotFreeInTerms us → x NotFreeInTerm (functerm f us)

data _NotFreeIn_ : Variable → Formula → Set where
  atom : ∀{x r} {ts : Vec Term (Relation.arity r)}
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
  ident   : ∀ α x → α [ x / varterm x ]≡ α
  atom    : ∀{x t}
              → (r : Relation) → {xs ys : Vec Term (Relation.arity r)}
              → [ xs ][ x / t ]≡ ys → (atom r xs) [ x / t ]≡ (atom r ys)
  _⇒_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ⇒ β) [ x / t ]≡ (α′ ⇒ β′)
  _∧_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∧ β) [ x / t ]≡ (α′ ∧ β′)
  _∨_     : ∀{α α′ β β′ x t}
              → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∨ β) [ x / t ]≡ (α′ ∨ β′)
  Λ∣      : ∀{t} → (x : Variable) → (α : Formula) → (Λ x α) [ x / t ]≡ (Λ x α)
  V∣      : ∀{t} → (x : Variable) → (α : Formula) → (V x α) [ x / t ]≡ (V x α)
  Λ       : ∀{α β x v t} → v ≢ x → x NotFreeInTerm t
              → α [ v / t ]≡ β → (Λ x α) [ v / t ]≡ (Λ x β)
  V       : ∀{α β x v t} → v ≢ x → x NotFreeInTerm t
              → α [ v / t ]≡ β → (V x α) [ v / t ]≡ (V x β)


data _FreeFor_In_ (t : Term) (x : Variable) : Formula → Set where
  atom : ∀ r us → t FreeFor x In atom r us
  _⇒_ : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ⇒ β
  _∧_ : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ∧ β
  _∨_ : ∀{α β} → t FreeFor x In α → t FreeFor x In β → t FreeFor x In α ∨ β
  Λ∣  : ∀ α → t FreeFor x In Λ x α
  V∣  : ∀ α → t FreeFor x In V x α
  Λ   : ∀ α y → y NotFreeInTerm t → t FreeFor x In α → t FreeFor x In Λ y α
  V   : ∀ α y → y NotFreeInTerm t → t FreeFor x In α → t FreeFor x In V y α

--------------------------------------------------------------------------------
-- Computation requires decidable equality for the types above

natEq : Decidable≡ ℕ
natEq zero zero = yes refl
natEq zero (suc m) = no λ ()
natEq (suc n) zero = no λ ()
natEq (suc n) (suc m) with natEq n m
...                   | yes refl = yes refl
...                   | no  neq  = no φ
                                   where φ : _
                                         φ refl = neq refl

varEq : Decidable≡ Variable
varEq (mkvar n) (mkvar m) with natEq n m
...                       | yes refl = yes refl
...                       | no  neq  = no φ
                                       where φ : _
                                             φ refl = neq refl

relEq : Decidable≡ Relation
relEq (mkrel n j) (mkrel m k) with natEq n m
...                           | no  neq  = no φ
                                            where φ : _
                                                  φ refl = neq refl
...                           | yes refl with natEq j k
...                                      | yes refl = yes refl
...                                      | no  neq  = no φ
                                                      where φ : _
                                                            φ refl = neq refl

funcEq : Decidable≡ Function
funcEq (mkfunc n j) (mkfunc m k) with natEq n m
...                              | no  neq  = no φ
                                              where φ : _
                                                    φ refl = neq refl
...                              | yes refl with natEq j k
...                                         | yes refl = yes refl
...                                         | no  neq  = no φ
                                                         where φ : _
                                                               φ refl = neq refl

vecEq : ∀{n} {A : Set} → Decidable≡ A → Decidable≡ (Vec A n)
vecEq eq [] [] = yes refl
vecEq eq (x ∷ xs) (y ∷ ys) with eq x y
...                        | no  neq  = no φ
                                        where φ : _
                                              φ refl = neq refl
...                        | yes refl with vecEq eq xs ys
...                                   | yes refl = yes refl
...                                   | no  neq  = no φ
                                                   where φ : _
                                                         φ refl = neq refl

termEq : Decidable≡ Term
termEq (varterm x)     (varterm y)     with varEq x y
...                                    | yes refl = yes refl
...                                    | no x≢y   = no φ
                                                    where φ : _
                                                          φ refl = x≢y refl
termEq (varterm x)     (functerm f ts) = no λ ()
termEq (functerm f ts) (varterm x)     = no λ ()
termEq (functerm f []) (functerm g []) with funcEq f g
...                                    | yes refl = yes refl
...                                    | no f≢g   = no φ
                                                    where φ : _
                                                          φ refl = f≢g refl
termEq (functerm f []) (functerm g (_ ∷ _)) = no λ ()
termEq (functerm f (_ ∷ _)) (functerm g []) = no λ ()
termEq
  (functerm (mkfunc n (suc j)) (u ∷ us)) (functerm (mkfunc m (suc k)) (v ∷ vs))
  with natEq j k
... | no n≢m   = no φ
                 where φ : _
                       φ refl = n≢m refl
... | yes refl with termEq u v
...   | no u≢v   = no φ
                   where φ : _
                         φ refl = u≢v refl
...   | yes refl
        with termEq (functerm (mkfunc n j) us) (functerm (mkfunc m k) vs)
...     | yes refl = yes refl
...     | no neq   = no φ
                     where φ : _
                           φ refl = neq refl

formulaEq : Decidable≡ Formula
formulaEq (atom r xs) (atom s ys)
    with natEq (Relation.arity r) (Relation.arity s)
... | no neq = no φ
               where φ : _
                     φ refl = neq refl
... | yes refl with (relEq r s) | (vecEq termEq xs ys)
...            | yes refl | yes refl = yes refl
...            | _        | no neq   = no φ
                                       where φ : _
                                             φ refl = neq refl
...            | no neq   | _        = no φ
                                       where φ : _
                                             φ refl = neq refl
formulaEq (α ⇒ β) (γ ⇒ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
formulaEq (α ∧ β) (γ ∧ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
formulaEq (α ∨ β) (γ ∨ δ) with (formulaEq α γ) | (formulaEq β δ)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
formulaEq (Λ x α) (Λ y β) with (varEq x y) | (formulaEq α β)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
formulaEq (V x α) (V y β) with (varEq x y) | (formulaEq α β)
...                       | yes refl | yes refl = yes refl
...                       | _        | no neq   = no φ
                                                  where φ : _
                                                        φ refl = neq refl
...                       | no neq   | _        = no φ
                                                  where φ : _
                                                        φ refl = neq refl
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



_notFreeInTerms_ : ∀{n} → (x : Variable) → (ts : Vec Term n)
                   → Dec (x NotFreeInTerms ts)
x notFreeInTerms [] = yes []
x notFreeInTerms (varterm y ∷ ts) with varEq x y
... | yes refl = no φ
                 where φ : _
                       φ (varterm nrefl ∷ _) = nrefl refl
... | no x≢y   with x notFreeInTerms ts
...            | yes xnfts = yes (varterm x≢y ∷ xnfts)
...            | no xfts   = no φ
                             where φ : _
                                   φ (_ ∷ xnfts) = xfts xnfts
x notFreeInTerms (functerm f us ∷ ts) with x notFreeInTerms us
... | no xfus   = no φ
                  where φ : _
                        φ (functerm xnfus ∷ _) = xfus xnfus
... | yes xnfus with x notFreeInTerms ts
...             | yes xnfts = yes (functerm xnfus ∷ xnfts)
...             | no xfts   = no φ
                              where φ : _
                                    φ (_ ∷ xnfts) = xfts xnfts


_notFreeInTerm_ : (x : Variable) → (t : Term) → Dec (x NotFreeInTerm t)
x notFreeInTerm t with x notFreeInTerms (t ∷ [])
x notFreeInTerm t | yes (pf ∷ []) = yes pf
x notFreeInTerm t | no npf        = no λ z → npf (z ∷ [])


_notFreeIn_ : (x : Variable) → (α : Formula) → Dec (x NotFreeIn α)
x notFreeIn atom r ts with x notFreeInTerms ts
x notFreeIn atom r ts | yes bdts = yes (atom bdts)
x notFreeIn atom r ts | no ¬bdts = no φ
                                   where
                                     φ : ¬(x NotFreeIn atom r ts)
                                     φ (atom bdts) = ¬bdts bdts
x notFreeIn (α ⇒ β)   with x notFreeIn α | x notFreeIn β
x notFreeIn (α ⇒ β)   | yes αbd | yes βbd = yes (αbd ⇒ βbd)
x notFreeIn (α ⇒ β)   | _       | no ¬βbd = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ⇒ β))
                                              φ (αbd ⇒ βbd) = ¬βbd βbd
x notFreeIn (α ⇒ β)   | no ¬αbd | _       = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ⇒ β))
                                              φ (αbd ⇒ βbd) = ¬αbd αbd
x notFreeIn (α ∧ β)   with x notFreeIn α | x notFreeIn β
x notFreeIn (α ∧ β)   | yes αbd | yes βbd = yes (αbd ∧ βbd)
x notFreeIn (α ∧ β)   | _       | no ¬βbd = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ∧ β))
                                              φ (αbd ∧ βbd) = ¬βbd βbd
x notFreeIn (α ∧ β)   | no ¬αbd | _       = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ∧ β))
                                              φ (αbd ∧ βbd) = ¬αbd αbd
x notFreeIn (α ∨ β)   with x notFreeIn α | x notFreeIn β
x notFreeIn (α ∨ β)   | yes αbd | yes βbd = yes (αbd ∨ βbd)
x notFreeIn (α ∨ β)   | _       | no ¬βbd = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ∨ β))
                                              φ (αbd ∨ βbd) = ¬βbd βbd
x notFreeIn (α ∨ β)   | no ¬αbd | _       = no φ
                                            where
                                              φ : ¬(x NotFreeIn (α ∨ β))
                                              φ (αbd ∨ βbd) = ¬αbd αbd
x notFreeIn Λ  y α    with varEq x y
x notFreeIn Λ .x α    | yes refl = yes (Λ∣ x α)
x notFreeIn Λ  y α    | no x≢y with x notFreeIn α
x notFreeIn Λ  y α    | no x≢y | yes αbd = yes (Λ y αbd)
x notFreeIn Λ  y α    | no x≢y | no ¬αbd = no φ
                                           where
                                             φ : ¬(x NotFreeIn Λ y α)
                                             φ (Λ∣ x α) = x≢y refl
                                             φ (Λ y αbd) = ¬αbd αbd
x notFreeIn V  y α    with varEq x y
x notFreeIn V .x α    | yes refl = yes (V∣ x α)
x notFreeIn V  y α    | no x≢y with x notFreeIn α
x notFreeIn V  y α    | no x≢y | yes αbd = yes (V y αbd)
x notFreeIn V  y α    | no x≢y | no ¬αbd = no φ
                                           where
                                             φ : ¬(x NotFreeIn V y α)
                                             φ (V∣ x α) = x≢y refl
                                             φ (V y αbd) = ¬αbd αbd


supFreeTerms : ∀{k} → (ts : Vec Term k) → Σ ℕ λ ⌈ts⌉ → ∀ n → ⌈ts⌉ < n
               → mkvar n NotFreeInTerms ts
supFreeTerms [] = zero , λ _ _ → []
supFreeTerms (varterm (mkvar m) ∷ ts) with supFreeTerms ts
... | ⌈ts⌉ , tspf with max m ⌈ts⌉
...               | less m≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    orderneq : ∀{n m} → n < m → mkvar m ≢ mkvar n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n
                    → All (mkvar n NotFreeInTerm_) (varterm (mkvar m) ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = varterm (orderneq (≤trans (sn≤sm m≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
...               | more ⌈ts⌉≤m = m , notFreeIsm
  where
    orderneq : ∀{n m} → n < m → mkvar m ≢ mkvar n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIsm : ∀ n → m < n
                 → All (mkvar n NotFreeInTerm_) (varterm (mkvar m) ∷ ts)
    notFreeIsm n m<n = varterm (orderneq m<n)
                       ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤m) m<n)
supFreeTerms (functerm f us     ∷ ts) with supFreeTerms us | supFreeTerms ts
... | ⌈us⌉ , uspf | ⌈ts⌉ , tspf with max ⌈us⌉ ⌈ts⌉
...                             | less ⌈us⌉≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n
                    → All (mkvar n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = functerm (uspf n (≤trans (sn≤sm ⌈us⌉≤⌈ts⌉) ⌈ts⌉<n))
                             ∷ tspf n ⌈ts⌉<n
...                             | more ⌈ts⌉≤⌈us⌉ = ⌈us⌉ , notFreeIs⌈us⌉
  where
    notFreeIs⌈us⌉ : ∀ n → ⌈us⌉ < n
                    → All (mkvar n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈us⌉ n ⌈us⌉<n = functerm (uspf n ⌈us⌉<n)
                             ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤⌈us⌉) ⌈us⌉<n)


supFreeTerm : ∀ t → Σ ℕ λ ⌈t⌉ → ∀ n → ⌈t⌉ < n → mkvar n NotFreeInTerm t
supFreeTerm t with supFreeTerms (t ∷ [])
supFreeTerm t | s , pfs = s , notFreeIss
  where
    notFreeIss : ∀ n → s < n → mkvar n NotFreeInTerm t
    notFreeIss n s<n with pfs n s<n
    notFreeIss n s<n | pf ∷ [] = pf


-- No guarantee that this notFree is tight - in fact for the V and Λ cases it is
-- not tight if the quantifier is the greatest variable (and does not have index
-- zero)
supFree : ∀ α → Σ ℕ λ ⌈α⌉ → ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn α
supFree (atom r ts) with supFreeTerms ts
supFree (atom r ts) | ⌈ts⌉ , tspf = ⌈ts⌉ , λ n ⌈ts⌉<n → atom (tspf n ⌈ts⌉<n)
supFree (α ⇒ β) with supFree α | supFree β
supFree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supFree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ⇒ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ⇒ βpf n ⌈β⌉<n
supFree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ⇒ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ⇒ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supFree (α ∧ β) with supFree α | supFree β
supFree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supFree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ∧ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∧ βpf n ⌈β⌉<n
supFree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ∧ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∧ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supFree (α ∨ β) with supFree α | supFree β
supFree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supFree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ∨ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∨ βpf n ⌈β⌉<n
supFree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ∨ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∨ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supFree (Λ x α) with supFree α
supFree (Λ x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → Λ x (αpf n ⌈α⌉<n)
supFree (V x α) with supFree α
supFree (V x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → V x (αpf n ⌈α⌉<n)


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


subNotFreeTerms : ∀{n x t} {us vs : Vec Term n} → x NotFreeInTerm t
                  → [ us ][ x / t ]≡ vs → x NotFreeInTerms vs
subNotFreeTerms xnft []                  = []
subNotFreeTerms xnft (varterm≡ ∷ ps)     = xnft ∷ subNotFreeTerms xnft ps
subNotFreeTerms xnft (varterm≢ neq ∷ ps) = varterm neq ∷ subNotFreeTerms xnft ps
subNotFreeTerms xnft (functerm sub ∷ ps) = functerm (subNotFreeTerms xnft sub)
                                           ∷ subNotFreeTerms xnft ps

subNotFree : ∀{α x t β} → x NotFreeInTerm t → α [ x / t ]≡ β → x NotFreeIn β
subNotFree (varterm x≢x) (ident   _    _) = ⊥-elim (x≢x refl)
subNotFree xnft (atom r p)       = atom (subNotFreeTerms xnft p)
subNotFree xnft (pα ⇒ pβ)        = subNotFree xnft pα ⇒ subNotFree xnft pβ
subNotFree xnft (pα ∧ pβ)        = subNotFree xnft pα ∧ subNotFree xnft pβ
subNotFree xnft (pα ∨ pβ)        = subNotFree xnft pα ∨ subNotFree xnft pβ
subNotFree xnft (Λ∣ y α)         = Λ∣ y α
subNotFree xnft (Λ x≢y ynft p)   = Λ _ (subNotFree xnft p)
subNotFree xnft (V∣ y α)         = V∣ y α
subNotFree xnft (V x≢y ynft p)   = V _ (subNotFree xnft p)
