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
  notfree : ∀{α x t} → x NotFreeIn α → α [ x / t ]≡ α
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

-- Decidablity proofs

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

_freeFor_In_ : ∀ t x α → Dec (t FreeFor x In α)
t freeFor x In α with x notFreeIn α
(t freeFor x In α) | yes xnfα = yes (notfree xnfα)
(t freeFor x In α) | no ¬xnfα = lemma α ¬xnfα
  where
    lemma : ∀ α → ¬(x NotFreeIn α)  → Dec (t FreeFor x In α)
    lemma (atom r ts) xf = yes (atom r ts)
    lemma (α ⇒ β)     xf with t freeFor x In α
    ...               | no ¬tffα = no ¬tffα⇒β
                                   where
                                     ¬tffα⇒β : _
                                     ¬tffα⇒β (notfree xnf) = xf xnf
                                     ¬tffα⇒β (tffα ⇒ _)     = ¬tffα tffα
    ...               | yes tffα with t freeFor x In β
    ...                          | no ¬tffβ = no ¬tffα⇒β
                                              where
                                                ¬tffα⇒β : _
                                                ¬tffα⇒β (notfree xnf) = xf xnf
                                                ¬tffα⇒β (_ ⇒ tffβ) = ¬tffβ tffβ
    ...                          | yes tffβ = yes (tffα ⇒ tffβ)
    lemma (α ∧ β)     xf with t freeFor x In α
    ...               | no ¬tffα = no ¬tffα∧β
                                   where
                                     ¬tffα∧β : _
                                     ¬tffα∧β (notfree xnf) = xf xnf
                                     ¬tffα∧β (tffα ∧ _)     = ¬tffα tffα
    ...               | yes tffα with t freeFor x In β
    ...                          | no ¬tffβ = no ¬tffα∧β
                                              where
                                                ¬tffα∧β : _
                                                ¬tffα∧β (notfree xnf) = xf xnf
                                                ¬tffα∧β (_ ∧ tffβ) = ¬tffβ tffβ
    ...                          | yes tffβ = yes (tffα ∧ tffβ)
    lemma (α ∨ β)     xf with t freeFor x In α
    ...               | no ¬tffα = no ¬tffα∨β
                                   where
                                     ¬tffα∨β : _
                                     ¬tffα∨β (notfree xnf) = xf xnf
                                     ¬tffα∨β (tffα ∨ _)     = ¬tffα tffα
    ...               | yes tffα with t freeFor x In β
    ...                          | no ¬tffβ = no ¬tffα∨β
                                              where
                                                ¬tffα∨β : _
                                                ¬tffα∨β (notfree xnf) = xf xnf
                                                ¬tffα∨β (_ ∨ tffβ) = ¬tffβ tffβ
    ...                          | yes tffβ = yes (tffα ∨ tffβ)
    lemma (Λ y α)     xf with varEq x y
    ...                  | yes refl = yes (Λ∣ α)
    ...                  | no  x≢y  with t freeFor x In α
    ...                             | no ¬tffα = no ¬tff
                                                 where
                                                   ¬tff : _
                                                   ¬tff (notfree xnf) = xf xnf
                                                   ¬tff (Λ∣ .α) = x≢y refl
                                                   ¬tff (Λ .α .y _ tffα) = ¬tffα tffα
    ...                             | yes tffα with y notFreeInTerm t
    ...                                        | yes ynft = yes (Λ α y ynft tffα)
    ...                                        | no ¬ynft = no ¬tff
                                                            where
                                                              ¬tff : _
                                                              ¬tff (notfree xnf) = xf xnf
                                                              ¬tff (Λ∣ .α) = x≢y refl
                                                              ¬tff (Λ .α .y ynft _) = ¬ynft ynft
    lemma (V y α)     xf with varEq x y
    ...                  | yes refl = yes (V∣ α)
    ...                  | no  x≢y  with t freeFor x In α
    ...                             | no ¬tffα = no ¬tff
                                                 where
                                                   ¬tff : _
                                                   ¬tff (notfree xnf) = xf xnf
                                                   ¬tff (V∣ .α) = x≢y refl
                                                   ¬tff (V .α .y _ tffα) = ¬tffα tffα
    ...                             | yes tffα with y notFreeInTerm t
    ...                                        | yes ynft = yes (V α y ynft tffα)
    ...                                        | no ¬ynft = no ¬tff
                                                            where
                                                              ¬tff : _
                                                              ¬tff (notfree xnf) = xf xnf
                                                              ¬tff (V∣ .α) = x≢y refl
                                                              ¬tff (V .α .y ynft _) = ¬ynft ynft


-- Generating not-free variables

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


minFresh : ∀ α → Σ ℕ λ ⌈α⌉ → ∀ n → ⌈α⌉ ≤ n → mkvar n FreshIn α
minFresh (atom r ts) with supFreeTerms ts
minFresh (atom r ts) | ⌈ts⌉ , tspf = suc ⌈ts⌉ , (λ n ⌈ts⌉≤n → atom (tspf n ⌈ts⌉≤n))
minFresh (α ⇒ β) with minFresh α | minFresh β
...              | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
...                                      | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , freshIs⌈β⌉
  where
    freshIs⌈β⌉ : ∀ n → ⌈β⌉ ≤ n → mkvar n FreshIn (α ⇒ β)
    freshIs⌈β⌉ n ⌈β⌉≤n = αpf n (≤trans ⌈α⌉≤⌈β⌉ ⌈β⌉≤n) ⇒ βpf n ⌈β⌉≤n
...                                      | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    freshIs⌈α⌉ : ∀ n → ⌈α⌉ ≤ n → mkvar n FreshIn (α ⇒ β)
    freshIs⌈α⌉ n ⌈α⌉≤n = αpf n ⌈α⌉≤n ⇒ βpf n (≤trans ⌈β⌉≤⌈α⌉ ⌈α⌉≤n)
minFresh (α ∧ β) with minFresh α | minFresh β
...              | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
...                                      | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , freshIs⌈β⌉
  where
    freshIs⌈β⌉ : ∀ n → ⌈β⌉ ≤ n → mkvar n FreshIn (α ∧ β)
    freshIs⌈β⌉ n ⌈β⌉≤n = αpf n (≤trans ⌈α⌉≤⌈β⌉ ⌈β⌉≤n) ∧ βpf n ⌈β⌉≤n
...                                      | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    freshIs⌈α⌉ : ∀ n → ⌈α⌉ ≤ n → mkvar n FreshIn (α ∧ β)
    freshIs⌈α⌉ n ⌈α⌉≤n = αpf n ⌈α⌉≤n ∧ βpf n (≤trans ⌈β⌉≤⌈α⌉ ⌈α⌉≤n)
minFresh (α ∨ β) with minFresh α | minFresh β
...              | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
...                                      | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , freshIs⌈β⌉
  where
    freshIs⌈β⌉ : ∀ n → ⌈β⌉ ≤ n → mkvar n FreshIn (α ∨ β)
    freshIs⌈β⌉ n ⌈β⌉≤n = αpf n (≤trans ⌈α⌉≤⌈β⌉ ⌈β⌉≤n) ∨ βpf n ⌈β⌉≤n
...                                      | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    freshIs⌈α⌉ : ∀ n → ⌈α⌉ ≤ n → mkvar n FreshIn (α ∨ β)
    freshIs⌈α⌉ n ⌈α⌉≤n = αpf n ⌈α⌉≤n ∨ βpf n (≤trans ⌈β⌉≤⌈α⌉ ⌈α⌉≤n)
minFresh (Λ (mkvar k) α) with minFresh α
...                      | ⌈α⌉ , αpf with max (suc k) ⌈α⌉
...                                  | less sk≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    skNewLemma : ∀{n m} → suc m ≤ n → mkvar n ≢ mkvar m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIs⌈α⌉ : ∀ n → ⌈α⌉ ≤ n → mkvar n FreshIn Λ (mkvar k) α
    freshIs⌈α⌉ n ⌈α⌉≤n = Λ (skNewLemma (≤trans sk≤⌈α⌉ ⌈α⌉≤n)) (αpf n ⌈α⌉≤n)
...                                  | more ⌈α⌉≤sk = suc k , freshIssk
  where
    skNewLemma : ∀{n m} → suc m ≤ n → mkvar n ≢ mkvar m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIssk : ∀ n → suc k ≤ n → mkvar n FreshIn Λ (mkvar k) α
    freshIssk n sk≤n = Λ (skNewLemma sk≤n) (αpf n (≤trans ⌈α⌉≤sk sk≤n))
minFresh (V (mkvar k) α) with minFresh α
...                      | ⌈α⌉ , αpf with max (suc k) ⌈α⌉
...                                  | less sk≤⌈α⌉ = ⌈α⌉ , freshIs⌈α⌉
  where
    skNewLemma : ∀{n m} → suc m ≤ n → mkvar n ≢ mkvar m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIs⌈α⌉ : ∀ n → ⌈α⌉ ≤ n → mkvar n FreshIn V (mkvar k) α
    freshIs⌈α⌉ n ⌈α⌉≤n = V (skNewLemma (≤trans sk≤⌈α⌉ ⌈α⌉≤n)) (αpf n ⌈α⌉≤n)
...                                  | more ⌈α⌉≤sk = suc k , freshIssk
  where
    skNewLemma : ∀{n m} → suc m ≤ n → mkvar n ≢ mkvar m
    skNewLemma (sn≤sm m<m) refl = skNewLemma m<m refl
    freshIssk : ∀ n → suc k ≤ n → mkvar n FreshIn V (mkvar k) α
    freshIssk n sk≤n = V (skNewLemma sk≤n) (αpf n (≤trans ⌈α⌉≤sk sk≤n))

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

subNotFreeIdent : ∀{α x t} → x NotFreeIn α → α [ x / t ]≡ α
subNotFreeIdent {atom r ts} {x} (atom xnfts) = atom r (termsLemma ts xnfts)
  where
    termsLemma : ∀{t n x} → (ts : Vec Term n) → x NotFreeInTerms ts → [ ts ][ x / t ]≡ ts
    termsLemma [] xnf = []
    termsLemma (.(varterm _) ∷ ts) (varterm neq ∷ xnfts) = varterm≢ neq ∷ termsLemma ts xnfts
    termsLemma (.(functerm _ _) ∷ ts) (functerm xnfus ∷ xnfts) = functerm (termsLemma _ xnfus) ∷ termsLemma ts xnfts
subNotFreeIdent {α ⇒ β} {x} (xnfα ⇒ xnfβ) = subNotFreeIdent xnfα ⇒ subNotFreeIdent xnfβ
subNotFreeIdent {α ∧ β} {x} (xnfα ∧ xnfβ) = subNotFreeIdent xnfα ∧ subNotFreeIdent xnfβ
subNotFreeIdent {α ∨ β} {x} (xnfα ∨ xnfβ) = subNotFreeIdent xnfα ∨ subNotFreeIdent xnfβ
subNotFreeIdent {Λ x α} {x} (Λ∣ .x .α)    = Λ∣ x α
subNotFreeIdent {Λ y α} {x} (Λ .y xnfα)   = notfree (Λ y xnfα)
subNotFreeIdent {V x α} {x} (V∣ .x .α)    = V∣ x α
subNotFreeIdent {V y α} {x} (V .y xnfα)   = notfree (V y xnfα)


_[_/_] : ∀{t} → ∀ α x → t FreeFor x In α → Σ Formula (α [ x / t ]≡_)
α [ x / notfree xnfα ]          = α , subNotFreeIdent xnfα
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


-- Make this a derived rule
ident : ∀ α x → α [ x / varterm x ]≡ α
ident (atom r ts) x = atom r (identTerms ts x)
  where
    identTerms : ∀{n} → (ts : Vec Term n) → ∀ x → [ ts ][ x / varterm x ]≡ ts
    identTerms [] x = []
    identTerms (varterm y ∷ ts) x with varEq x y
    ...                           | yes refl = varterm≡ ∷ identTerms ts x
    ...                           | no  x≢y  = varterm≢ x≢y ∷ identTerms ts x
    identTerms (functerm f us ∷ ts) x = functerm (identTerms us x) ∷ identTerms ts x
ident (α ⇒ β) x = ident α x ⇒ ident β x
ident (α ∧ β) x = ident α x ∧ ident β x
ident (α ∨ β) x = ident α x ∨ ident β x
ident (Λ y α) x with varEq x y
...             | yes refl = Λ∣ y α
...             | no  x≢y  = Λ x≢y (varterm y≢x) (ident α x)
                             where
                               y≢x : y ≢ x
                               y≢x refl = x≢y refl
ident (V y α) x with varEq x y
...             | yes refl = V∣ y α
...             | no  x≢y  = V x≢y (varterm y≢x) (ident α x)
                             where
                               y≢x : y ≢ x
                               y≢x refl = x≢y refl

subNotFreeTerms : ∀{n x t} {us vs : Vec Term n} → x NotFreeInTerm t
                  → [ us ][ x / t ]≡ vs → x NotFreeInTerms vs
subNotFreeTerms xnft []                  = []
subNotFreeTerms xnft (varterm≡ ∷ ps)     = xnft ∷ subNotFreeTerms xnft ps
subNotFreeTerms xnft (varterm≢ neq ∷ ps) = varterm neq ∷ subNotFreeTerms xnft ps
subNotFreeTerms xnft (functerm sub ∷ ps) = functerm (subNotFreeTerms xnft sub)
                                           ∷ subNotFreeTerms xnft ps

subNotFree : ∀{α x t β} → x NotFreeInTerm t → α [ x / t ]≡ β → x NotFreeIn β
subNotFree xnft (notfree xnfα)   = xnfα
subNotFree xnft (atom r p)       = atom (subNotFreeTerms xnft p)
subNotFree xnft (pα ⇒ pβ)        = subNotFree xnft pα ⇒ subNotFree xnft pβ
subNotFree xnft (pα ∧ pβ)        = subNotFree xnft pα ∧ subNotFree xnft pβ
subNotFree xnft (pα ∨ pβ)        = subNotFree xnft pα ∨ subNotFree xnft pβ
subNotFree xnft (Λ∣ y α)         = Λ∣ y α
subNotFree xnft (Λ x≢y ynft p)   = Λ _ (subNotFree xnft p)
subNotFree xnft (V∣ y α)         = V∣ y α
subNotFree xnft (V x≢y ynft p)   = V _ (subNotFree xnft p)

subInverse : ∀ α x ω β → ω NotFreeIn α → α [ x / varterm ω ]≡ β → β [ ω / varterm x ]≡ α
subInverse α x ω β ωnfα (notfree xnfα) = notfree ωnfα
subInverse (atom .r us) x ω (atom .r vs) (atom x₂) (atom r x₁) = atom r (termsLemma us vs x ω x₂ x₁)
  where
    termsLemma : ∀{n} → (us vs : Vec Term n) → ∀ x ω → ω NotFreeInTerms us → [ us ][ x / varterm ω ]≡ vs → [ vs ][ ω / varterm x ]≡ us
    termsLemma [] .[] x ω x₁ [] = []
    termsLemma (.(varterm x) ∷ us) (.(varterm ω) ∷ vs) x ω (x₁ ∷ x₅) (varterm≡ ∷ x₄) = varterm≡ ∷ termsLemma us vs x ω x₅ x₄
    termsLemma ((varterm y) ∷ us) ((varterm .y) ∷ vs) x ω (x₁ ∷ x₅) (varterm≢ x₂ ∷ x₄) with varEq ω y
    termsLemma (varterm y ∷ us) (varterm .y ∷ vs) x .y (varterm x₁ ∷ x₅) (varterm≢ x₂ ∷ x₄) | yes refl = ⊥-elim (x₁ refl)
    termsLemma (varterm y ∷ us) (varterm .y ∷ vs) x ω (x₁ ∷ x₅) (varterm≢ x₂ ∷ x₄) | no x₃ = varterm≢ x₃ ∷ termsLemma us vs x ω x₅ x₄
    termsLemma (functerm f ts ∷ us) (functerm .f ss ∷ vs) x ω (functerm x₁ ∷ x₅) (functerm x₂ ∷ x₄) = functerm (termsLemma ts ss x ω x₁ x₂) ∷ termsLemma us vs x ω x₅ x₄
subInverse (α ⇒ β) x ω (α′ ⇒ β′) (ωnfα ⇒ ωnfβ) (repα ⇒ repβ) = subInverse α x ω α′ ωnfα repα ⇒ subInverse β x ω β′ ωnfβ repβ
subInverse (α ∧ β) x ω (α′ ∧ β′) (ωnfα ∧ ωnfβ) (repα ∧ repβ) = subInverse α x ω α′ ωnfα repα ∧ subInverse β x ω β′ ωnfβ repβ
subInverse (α ∨ β) x ω (α′ ∨ β′) (ωnfα ∨ ωnfβ) (repα ∨ repβ) = subInverse α x ω α′ ωnfα repα ∨ subInverse β x ω β′ ωnfβ repβ
subInverse .(Λ x α) x ω .(Λ x α) q (Λ∣ .x α) = subNotFreeIdent q
subInverse .(V x α) x .x .(V x α) (V∣ .x .α) (V∣ .x α) = ident (V x α) x
subInverse .(V x α) x ω .(V x α) (V .x ωnfα) (V∣ .x α) = subNotFreeIdent (V x ωnfα)
subInverse (Λ y _) x ω (Λ .y _) ωnfα (Λ x₁ x₂ rep) with varEq ω y
subInverse (Λ y α) x .y (Λ .y β) ωnfα (Λ x₁ (varterm x₂) rep) | yes refl = ⊥-elim (x₂ refl)
subInverse (Λ y α) x .y (Λ .y β) (Λ∣ .y .α) (Λ x₁ x₂ rep) | no x₃ = ⊥-elim (x₃ refl)
subInverse (Λ y α) x ω (Λ .y β) (Λ .y ωnfα) (Λ x₁ x₂ rep) | no x₃ = Λ x₃ (varterm (≢sym x y x₁)) (subInverse α x ω β ωnfα rep)
  where ≢sym : (x y : Variable) → x ≢ y → y ≢ x
        ≢sym x y x≢y refl = x≢y refl
subInverse .(V ω α) x ω .(V ω _) (V∣ .ω α) (V x₁ (varterm x₂) rep) = ⊥-elim (x₂ refl)
subInverse (V .y α) x ω (V .y β) (V y ωnfα) (V x₁ x₂ rep) with varEq ω y
subInverse (V .y α) x .y (V .y β) (V y ωnfα) (V x₁ (varterm x₂) rep) | yes refl = ⊥-elim (x₂ refl)
subInverse (V .y α) x ω (V .y β) (V y ωnfα) (V x₁ x₂ rep) | no x₃ = V x₃ (varterm (≢sym x y x₁)) (subInverse α x ω β ωnfα rep)
  where ≢sym : (x y : Variable) → x ≢ y → y ≢ x
        ≢sym x y x≢y refl = x≢y refl

freshNotFree : ∀{α x} → x FreshIn α → x NotFreeIn α
freshNotFree (atom x) = atom x
freshNotFree (xfrα ⇒ xfrα₁) = freshNotFree xfrα ⇒ freshNotFree xfrα₁
freshNotFree (xfrα ∧ xfrα₁) = freshNotFree xfrα ∧ freshNotFree xfrα₁
freshNotFree (xfrα ∨ xfrα₁) = freshNotFree xfrα ∨ freshNotFree xfrα₁
freshNotFree (Λ x xfrα) = Λ _ (freshNotFree xfrα)
freshNotFree (V x xfrα) = V _ (freshNotFree xfrα)

freshFreeFor : ∀{α x y} → x FreshIn α → (varterm x) FreeFor y In α
freshFreeFor (atom x) = atom _ _
freshFreeFor (xfrα ⇒ xfrα₁) = freshFreeFor xfrα ⇒ freshFreeFor xfrα₁
freshFreeFor (xfrα ∧ xfrα₁) = freshFreeFor xfrα ∧ freshFreeFor xfrα₁
freshFreeFor (xfrα ∨ xfrα₁) = freshFreeFor xfrα ∨ freshFreeFor xfrα₁
freshFreeFor (Λ x xfrα) = Λ _ _ (varterm (≢sym _ _ x)) (freshFreeFor xfrα)
  where ≢sym : (x y : Variable) → x ≢ y → y ≢ x
        ≢sym x y x≢y refl = x≢y refl
freshFreeFor (V x xfrα) = V _ _ (varterm (≢sym _ _ x)) (freshFreeFor xfrα)
  where ≢sym : (x y : Variable) → x ≢ y → y ≢ x
        ≢sym x y x≢y refl = x≢y refl

subUniqueTerms : ∀{n} → (us : Vec Term n) → ∀{x t} → {vs ws : Vec Term n} → [ us ][ x / t ]≡ vs → [ us ][ x / t ]≡ ws → vs ≡ ws
subUniqueTerms [] [] [] = refl
subUniqueTerms (varterm x ∷ us) (varterm≡ ∷ p) (varterm≡ ∷ q) with subUniqueTerms us p q
subUniqueTerms (varterm x ∷ us) (varterm≡ ∷ p) (varterm≡ ∷ q) | refl = refl
subUniqueTerms (varterm x ∷ us) (varterm≡ ∷ p) (varterm≢ x₁ ∷ q) = ⊥-elim (x₁ refl)
subUniqueTerms (varterm x ∷ us) (varterm≢ x₁ ∷ p) (varterm≡ ∷ q) = ⊥-elim (x₁ refl)
subUniqueTerms (varterm x ∷ us) (varterm≢ x₁ ∷ p) (varterm≢ x₂ ∷ q) with subUniqueTerms us p q
subUniqueTerms (varterm x ∷ us) (varterm≢ x₁ ∷ p) (varterm≢ x₂ ∷ q) | refl = refl
subUniqueTerms (functerm f ts ∷ us) (functerm x ∷ p) (functerm x₁ ∷ q) with subUniqueTerms ts x x₁ | subUniqueTerms us p q
subUniqueTerms (functerm f ts ∷ us) (functerm x ∷ p) (functerm x₁ ∷ q) | refl | refl = refl

subNotFreeIdentTerms : ∀{n x t} → (us : Vec Term n) → x NotFreeInTerms us → [ us ][ x / t ]≡ us
subNotFreeIdentTerms [] x = []
subNotFreeIdentTerms (varterm x₁ ∷ us) (varterm x ∷ x₂) = varterm≢ x ∷ subNotFreeIdentTerms us x₂
subNotFreeIdentTerms (functerm f ts ∷ us) (functerm x ∷ x₁) = functerm (subNotFreeIdentTerms ts x) ∷ subNotFreeIdentTerms us x₁

subUnique : ∀ α → ∀{x t β γ} → α [ x / t ]≡ β → α [ x / t ]≡ γ → β ≡ γ
subUnique (atom r ts) (notfree x) (notfree x₁) = refl
subUnique (atom r ts) (notfree (atom x)) (atom .r x₁) with subUniqueTerms ts (subNotFreeIdentTerms ts x) x₁
subUnique (atom r ts) (notfree (atom x)) (atom .r x₁) | refl = refl
subUnique (atom r ts) (atom .r x) (notfree (atom x₁)) with subUniqueTerms ts (subNotFreeIdentTerms ts x₁) x
subUnique (atom r ts) (atom .r x) (notfree (atom x₁)) | refl = refl
subUnique (atom r ts) (atom .r x) (atom .r x₁) with subUniqueTerms ts x x₁
subUnique (atom r ts) (atom .r x) (atom .r x₁) | refl = refl
subUnique (α ⇒ β) (notfree (x₁ ⇒ x₂)) (notfree (y₁ ⇒ y₂)) = refl
subUnique (α ⇒ β) (notfree (x₁ ⇒ x₂)) (q₁ ⇒ q₂) with subUnique α (notfree x₁) q₁ | subUnique β (notfree x₂) q₂
subUnique (α ⇒ β) (notfree (x₁ ⇒ x₂)) (q₁ ⇒ q₂) | refl | refl = refl
subUnique (α ⇒ β) (p₁ ⇒ p₂) (notfree (y₁ ⇒ y₂)) with subUnique α p₁ (notfree y₁) | subUnique β p₂ (notfree y₂)
subUnique (α ⇒ β) (p₁ ⇒ p₂) (notfree (y₁ ⇒ y₂)) | refl | refl = refl
subUnique (α ⇒ β) (p₁ ⇒ p₂) (q₁ ⇒ q₂)           with subUnique α p₁ q₁ | subUnique β p₂ q₂
subUnique (α ⇒ β) (p₁ ⇒ p₂) (q₁ ⇒ q₂)           | refl | refl = refl
subUnique (α ∧ β) (notfree (x₁ ∧ x₂)) (notfree (y₁ ∧ y₂)) = refl
subUnique (α ∧ β) (notfree (x₁ ∧ x₂)) (q₁ ∧ q₂) with subUnique α (notfree x₁) q₁ | subUnique β (notfree x₂) q₂
subUnique (α ∧ β) (notfree (x₁ ∧ x₂)) (q₁ ∧ q₂) | refl | refl = refl
subUnique (α ∧ β) (p₁ ∧ p₂) (notfree (y₁ ∧ y₂)) with subUnique α p₁ (notfree y₁) | subUnique β p₂ (notfree y₂)
subUnique (α ∧ β) (p₁ ∧ p₂) (notfree (y₁ ∧ y₂)) | refl | refl = refl
subUnique (α ∧ β) (p₁ ∧ p₂) (q₁ ∧ q₂)           with subUnique α p₁ q₁ | subUnique β p₂ q₂
subUnique (α ∧ β) (p₁ ∧ p₂) (q₁ ∧ q₂)           | refl | refl = refl
subUnique (α ∨ β) (notfree (x₁ ∨ x₂)) (notfree (y₁ ∨ y₂)) = refl
subUnique (α ∨ β) (notfree (x₁ ∨ x₂)) (q₁ ∨ q₂) with subUnique α (notfree x₁) q₁ | subUnique β (notfree x₂) q₂
subUnique (α ∨ β) (notfree (x₁ ∨ x₂)) (q₁ ∨ q₂) | refl | refl = refl
subUnique (α ∨ β) (p₁ ∨ p₂) (notfree (y₁ ∨ y₂)) with subUnique α p₁ (notfree y₁) | subUnique β p₂ (notfree y₂)
subUnique (α ∨ β) (p₁ ∨ p₂) (notfree (y₁ ∨ y₂)) | refl | refl = refl
subUnique (α ∨ β) (p₁ ∨ p₂) (q₁ ∨ q₂)           with subUnique α p₁ q₁ | subUnique β p₂ q₂
subUnique (α ∨ β) (p₁ ∨ p₂) (q₁ ∨ q₂)           | refl | refl = refl
subUnique (Λ x α) (notfree x₁) (notfree x₂) = refl
subUnique (Λ x α) (notfree x₁) (Λ∣ .x .α) = refl
subUnique (Λ x α) (notfree (Λ∣ .x .α)) (Λ x₂ x₃ q) = ⊥-elim (x₂ refl)
subUnique (Λ x α) (notfree (Λ .x x₁)) (Λ x₂ x₃ q) with subUnique α (notfree x₁) q
subUnique (Λ x α) (notfree (Λ .x x₁)) (Λ x₂ x₃ q) | refl = refl
subUnique (Λ x α) (Λ∣ .x .α) (notfree x₁) = refl
subUnique (Λ x α) (Λ∣ .x .α) (Λ∣ .x .α) = refl
subUnique (Λ x α) (Λ∣ .x .α) (Λ x₁ x₂ q) = ⊥-elim (x₁ refl)
subUnique (Λ x α) (Λ x₁ x₂ p) (notfree (Λ∣ .x .α)) = ⊥-elim (x₁ refl)
subUnique (Λ x α) (Λ x₁ x₂ p) (notfree (Λ .x x₃)) with subUnique α p (notfree x₃)
subUnique (Λ x α) (Λ x₁ x₂ p) (notfree (Λ .x x₃)) | refl = refl
subUnique (Λ x α) (Λ x₁ x₂ p) (Λ∣ .x .α) = ⊥-elim (x₁ refl)
subUnique (Λ x α) (Λ x₁ x₂ p) (Λ x₃ x₄ q) with subUnique α p q
subUnique (Λ x α) (Λ x₁ x₂ p) (Λ x₃ x₄ q) | refl = refl
subUnique (V x α) (notfree x₁) (notfree x₂) = refl
subUnique (V x α) (notfree x₁) (V∣ .x .α) = refl
subUnique (V x α) (notfree (V∣ .x .α)) (V x₂ x₃ q) = ⊥-elim (x₂ refl)
subUnique (V x α) (notfree (V .x x₁)) (V x₂ x₃ q) with subUnique α (notfree x₁) q
subUnique (V x α) (notfree (V .x x₁)) (V x₂ x₃ q) | refl = refl
subUnique (V x α) (V∣ .x .α) (notfree x₁) = refl
subUnique (V x α) (V∣ .x .α) (V∣ .x .α) = refl
subUnique (V x α) (V∣ .x .α) (V x₁ x₂ q) = ⊥-elim (x₁ refl)
subUnique (V x α) (V x₁ x₂ p) (notfree (V∣ .x .α)) = ⊥-elim (x₁ refl)
subUnique (V x α) (V x₁ x₂ p) (notfree (V .x x₃)) with subUnique α p (notfree x₃)
subUnique (V x α) (V x₁ x₂ p) (notfree (V .x x₃)) | refl = refl
subUnique (V x α) (V x₁ x₂ p) (V∣ .x .α) = ⊥-elim (x₁ refl)
subUnique (V x α) (V x₁ x₂ p) (V x₃ x₄ q) with subUnique α p q
subUnique (V x α) (V x₁ x₂ p) (V x₃ x₄ q) | refl = refl
