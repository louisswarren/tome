module Formula where

open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_<_)
open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Vec
open import Decidable


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

data _NotFreeInTerm_ (x : Variable) where
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


-- Variable replacement

data [_][_/_]≡_ : ∀{n} → Vec Term n → Variable → Term → Vec Term n → Set

data ⟨_⟩[_/_]≡_ : Term → Variable → Term → Term → Set where
  varterm≡ : ∀{x t} → ⟨ varterm x ⟩[ x / t ]≡ t
  varterm≢ : ∀{x t y} → x ≢ y → ⟨ varterm y ⟩[ x / t ]≡ varterm y
  functerm : ∀{x t f us vs}
              → [ us ][ x  / t ]≡ vs → ⟨ functerm f us ⟩[ x / t ]≡ functerm f vs

data [_][_/_]≡_ where
  []  : ∀{x t} → [ [] ][ x / t ]≡ []
  _∷_ : ∀{x t u v n} {us vs : Vec Term n}
        → ⟨ u ⟩[ x / t ]≡ v → [ us ][ x / t ]≡ vs → [ u ∷ us ][ x / t ]≡ (v ∷ vs)

data _[_/_]≡_ : Formula → Variable → Term → Formula → Set where
  ident : ∀ α x → α [ x / varterm x ]≡ α
  atom  : ∀{x t}
            → (r : Relation) → {xs ys : Vec Term (Relation.arity r)}
            → [ xs ][ x / t ]≡ ys → (atom r xs) [ x / t ]≡ (atom r ys)
  _⇒_   : ∀{α α′ β β′ x t}
            → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ⇒ β) [ x / t ]≡ (α′ ⇒ β′)
  _∧_   : ∀{α α′ β β′ x t}
            → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∧ β) [ x / t ]≡ (α′ ∧ β′)
  _∨_   : ∀{α α′ β β′ x t}
            → α [ x / t ]≡ α′ → β [ x / t ]≡ β′ → (α ∨ β) [ x / t ]≡ (α′ ∨ β′)
  Λ∣    : ∀{t} → (x : Variable) → (α : Formula) → (Λ x α) [ x / t ]≡ (Λ x α)
  V∣    : ∀{t} → (x : Variable) → (α : Formula) → (V x α) [ x / t ]≡ (V x α)
  Λ     : ∀{α β x v t} → v ≢ x → x NotFreeInTerm t → α [ v / t ]≡ β → (Λ x α) [ v / t ]≡ (Λ x β)
  V     : ∀{α β x v t} → v ≢ x → x NotFreeInTerm t → α [ v / t ]≡ β → (V x α) [ v / t ]≡ (V x β)
  Λ/    : ∀{α β γ x v t ω} → ω NotFreeIn α → v ≢ ω → ω NotFreeInTerm t
          → α [ x / varterm ω ]≡ β → β [ v / t ]≡ γ → (Λ x α) [ v / t ]≡ (Λ ω γ)
  V/    : ∀{α β γ x v t ω} → ω NotFreeIn α → v ≢ ω → ω NotFreeInTerm t
          → α [ x / varterm ω ]≡ β → β [ v / t ]≡ γ → (V x α) [ v / t ]≡ (V ω γ)


--------------------------------------------------------------------------------
-- Computation requires decidable equality for the types above
-- Surely there's something nicer than this?

natEq : Decidable≡ ℕ
natEq zero zero = yes refl
natEq zero (suc m) = no (λ ())
natEq (suc n) zero = no (λ ())
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
termEq (varterm x) (varterm y) with varEq x y
...                             | yes refl = yes refl
...                             | no  neq  = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (varterm _) (functerm _ _) = no λ ()
termEq (functerm _ _) (varterm _) = no (λ ())
termEq (functerm (mkfunc n .0) []) (functerm (mkfunc m .0) []) with natEq n m
termEq (functerm (mkfunc n _) []) (functerm (mkfunc .n _) []) | yes refl = yes refl
termEq (functerm (mkfunc n _) []) (functerm (mkfunc m _) []) | no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (functerm (mkfunc _ .0) []) (functerm (mkfunc _ .(suc _)) (_ ∷ _)) = no (λ ())
termEq (functerm (mkfunc _ .(suc _)) (_ ∷ _)) (functerm (mkfunc _ .0) []) = no (λ ())
termEq (functerm (mkfunc n (suc k)) (x ∷ xs)) (functerm (mkfunc m (suc j)) (y ∷ ys)) with (natEq n m) , (natEq k j)
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (y ∷ ys)) | yes refl , yes refl with termEq (functerm (mkfunc n j) xs) (functerm (mkfunc n j) ys)
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (y ∷ .xs)) | yes refl , yes refl | yes refl with termEq x y
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (.x ∷ .xs)) | yes refl , yes refl | yes refl | yes refl = yes refl
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (y ∷ .xs)) | yes refl , yes refl | yes refl | no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (functerm (mkfunc n (suc .j)) (x ∷ xs)) (functerm (mkfunc .n (suc j)) (y ∷ ys)) | yes refl , yes refl | no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (functerm (mkfunc n (suc k)) (x ∷ xs)) (functerm (mkfunc m (suc j)) (y ∷ ys)) | _ , no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
termEq (functerm (mkfunc n (suc k)) (x ∷ xs)) (functerm (mkfunc m (suc j)) (y ∷ ys)) | no neq , _ = no φ
                                             where φ : _
                                                   φ refl = neq refl

formulaEq : Decidable≡ Formula
formulaEq (atom r xs) (atom s ys) with natEq (Relation.arity r) (Relation.arity s)
...                               | yes refl with (relEq r s) , (vecEq termEq xs ys)
...                                          | yes refl , yes refl = yes refl
...                                          | _ , no neq = no φ
                                                            where φ : _
                                                                  φ refl = neq refl
...                                          | no neq , _ = no φ
                                                            where φ : _
                                                                  φ refl = neq refl
formulaEq (atom r xs) (atom s ys) | no neq = no φ
                                             where φ : _
                                                   φ refl = neq refl
formulaEq (α ⇒ β) (γ ⇒ δ) with (formulaEq α γ) , (formulaEq β δ)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (α ∧ β) (γ ∧ δ) with (formulaEq α γ) , (formulaEq β δ)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (α ∨ β) (γ ∨ δ) with (formulaEq α γ) , (formulaEq β δ)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (Λ x α) (Λ y β) with (varEq x y) , (formulaEq α β)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (V x α) (V y β) with (varEq x y) , (formulaEq α β)
...                       | yes refl , yes refl = yes refl
...                       | _ , no neq = no φ
                                         where φ : _
                                               φ refl = neq refl
...                       | no neq , _ = no φ
                                         where φ : _
                                               φ refl = neq refl
formulaEq (atom r x) (β ⇒ β₁)   = no (λ ())
formulaEq (atom r x) (β ∧ β₁)   = no (λ ())
formulaEq (atom r x) (β ∨ β₁)   = no (λ ())
formulaEq (atom r x) (Λ x₁ β)   = no (λ ())
formulaEq (atom r x) (V x₁ β)   = no (λ ())
formulaEq (α ⇒ α₁)   (atom r x) = no (λ ())
formulaEq (α ⇒ α₁)   (β ∧ β₁)   = no (λ ())
formulaEq (α ⇒ α₁)   (β ∨ β₁)   = no (λ ())
formulaEq (α ⇒ α₁)   (Λ x β)    = no (λ ())
formulaEq (α ⇒ α₁)   (V x β)    = no (λ ())
formulaEq (α ∧ α₁)   (atom r x) = no (λ ())
formulaEq (α ∧ α₁)   (β ⇒ β₁)   = no (λ ())
formulaEq (α ∧ α₁)   (β ∨ β₁)   = no (λ ())
formulaEq (α ∧ α₁)   (Λ x β)    = no (λ ())
formulaEq (α ∧ α₁)   (V x β)    = no (λ ())
formulaEq (α ∨ α₁)   (atom r x) = no (λ ())
formulaEq (α ∨ α₁)   (β ⇒ β₁)   = no (λ ())
formulaEq (α ∨ α₁)   (β ∧ β₁)   = no (λ ())
formulaEq (α ∨ α₁)   (Λ x β)    = no (λ ())
formulaEq (α ∨ α₁)   (V x β)    = no (λ ())
formulaEq (Λ x α)   (atom r x₁) = no (λ ())
formulaEq (Λ x α)   (β ⇒ β₁)    = no (λ ())
formulaEq (Λ x α)   (β ∧ β₁)    = no (λ ())
formulaEq (Λ x α)   (β ∨ β₁)    = no (λ ())
formulaEq (Λ x α)   (V x₁ β)    = no (λ ())
formulaEq (V x α)   (atom r x₁) = no (λ ())
formulaEq (V x α)   (β ⇒ β₁)    = no (λ ())
formulaEq (V x α)   (β ∧ β₁)    = no (λ ())
formulaEq (V x α)   (β ∨ β₁)    = no (λ ())
formulaEq (V x α)   (Λ x₁ β)    = no (λ ())


--------------------------------------------------------------------------------

data _≤_ : ℕ → ℕ → Set where
  0≤n    : ∀{n} → zero ≤ n
  sn≤sm : ∀{n m} → n ≤ m → (suc n) ≤ (suc m)

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

¬<refl : ∀{n} → ¬(n < n)
¬<refl {zero} ()
¬<refl {suc n} (sn≤sm x) = ¬<refl x

≤refl : ∀{n} → n ≤ n
≤refl {zero}  = 0≤n
≤refl {suc n} = sn≤sm ≤refl

≤trans : ∀{x y z} → x ≤ y → y ≤ z → x ≤ z
≤trans 0≤n y≤z = 0≤n
≤trans (sn≤sm x≤y) (sn≤sm y≤z) = sn≤sm (≤trans x≤y y≤z)

data Max (n m : ℕ) : Set where
  less : n ≤ m → Max n m
  more : m ≤ n → Max n m

max : ∀ n m → Max n m
max zero    m       = less 0≤n
max (suc n) zero    = more 0≤n
max (suc n) (suc m) with max n m
max (suc n) (suc m) | less n≤m = less (sn≤sm n≤m)
max (suc n) (suc m) | more m≤n = more (sn≤sm m≤n)


_notFreeInTerms_ : ∀{n} → (x : Variable) → (ts : Vec Term n) → Dec (x NotFreeInTerms ts)
x notFreeInTerms []                   = yes []
x notFreeInTerms (t ∷ ts)             with x notFreeInTerms ts
x notFreeInTerms (t ∷ ts)             | no ¬rst = no φ
  where
    φ : ¬(All (x NotFreeInTerm_) (t ∷ ts))
    φ (_ ∷ rst) = ¬rst rst
x notFreeInTerms (varterm y ∷ ts)     | yes rst with varEq x y
x notFreeInTerms (varterm .x ∷ ts)    | yes rst | yes refl = no φ
  where
    φ : ¬(All (x NotFreeInTerm_) (varterm x ∷ ts))
    φ (varterm x≢x ∷ _) = x≢x refl
x notFreeInTerms (varterm y ∷ ts)     | yes rst | no x≢y = yes (varterm x≢y ∷ rst)
x notFreeInTerms (functerm f us ∷ ts) | yes rst with x notFreeInTerms us
x notFreeInTerms (functerm f us ∷ ts) | yes rst | yes uspf = yes (functerm uspf ∷ rst)
x notFreeInTerms (functerm f us ∷ ts) | yes rst | no ¬uspf = no φ
  where
    φ : ¬(All (x NotFreeInTerm_) (functerm f us ∷ ts))
    φ (functerm uspf ∷ _) = ¬uspf uspf


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


supfreeterms : ∀{k} → (ts : Vec Term k) → Σ ℕ λ ⌈ts⌉ → ∀ n → ⌈ts⌉ < n → mkvar n NotFreeInTerms ts
supfreeterms [] = zero , λ _ _ → []
supfreeterms (varterm (mkvar m) ∷ ts) with supfreeterms ts
... | ⌈ts⌉ , tspf with max m ⌈ts⌉
...               | less m≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    orderneq : ∀{n m} → n < m → mkvar m ≢ mkvar n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n → All (mkvar n NotFreeInTerm_) (varterm (mkvar m) ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = varterm (orderneq (≤trans (sn≤sm m≤⌈ts⌉) ⌈ts⌉<n)) ∷ tspf n ⌈ts⌉<n
...               | more ⌈ts⌉≤m = m , notFreeIsm
  where
    orderneq : ∀{n m} → n < m → mkvar m ≢ mkvar n
    orderneq {zero} {.0} () refl
    orderneq {suc n} {.(suc n)} (sn≤sm x) refl = orderneq x refl
    notFreeIsm : ∀ n → m < n → All (mkvar n NotFreeInTerm_) (varterm (mkvar m) ∷ ts)
    notFreeIsm n m<n = varterm (orderneq m<n) ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤m) m<n)
supfreeterms (functerm f us     ∷ ts) with supfreeterms us | supfreeterms ts
... | ⌈us⌉ , uspf | ⌈ts⌉ , tspf with max ⌈us⌉ ⌈ts⌉
...                             | less ⌈us⌉≤⌈ts⌉ = ⌈ts⌉ , notFreeIs⌈ts⌉
  where
    notFreeIs⌈ts⌉ : ∀ n → ⌈ts⌉ < n → All (mkvar n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈ts⌉ n ⌈ts⌉<n = functerm (uspf n (≤trans (sn≤sm ⌈us⌉≤⌈ts⌉) ⌈ts⌉<n)) ∷ tspf n ⌈ts⌉<n
...                             | more ⌈ts⌉≤⌈us⌉ = ⌈us⌉ , notFreeIs⌈us⌉
  where
    notFreeIs⌈us⌉ : ∀ n → ⌈us⌉ < n → All (mkvar n NotFreeInTerm_) (functerm f us ∷ ts)
    notFreeIs⌈us⌉ n ⌈us⌉<n = functerm (uspf n ⌈us⌉<n) ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤⌈us⌉) ⌈us⌉<n)


supfreeterm : ∀ t → Σ ℕ λ ⌈t⌉ → ∀ n → ⌈t⌉ < n → mkvar n NotFreeInTerm t
supfreeterm t with supfreeterms (t ∷ [])
supfreeterm t | s , pfs = s , notFreeIss
  where
    notFreeIss : ∀ n → s < n → mkvar n NotFreeInTerm t
    notFreeIss n s<n with pfs n s<n
    notFreeIss n s<n | pf ∷ [] = pf


-- No guarantee that this notFree is tight - in fact for the V and Λ cases it is
-- not tight if the quantifier is the greatest variable (and does not have index
-- zero)
supfree : ∀ α → Σ ℕ λ ⌈α⌉ → ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn α
supfree (atom r ts) with supfreeterms ts
supfree (atom r ts) | ⌈ts⌉ , tspf = ⌈ts⌉ , λ n ⌈ts⌉<n → atom (tspf n ⌈ts⌉<n)
supfree (α ⇒ β) with supfree α | supfree β
supfree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supfree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ⇒ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ⇒ βpf n ⌈β⌉<n
supfree (α ⇒ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ⇒ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ⇒ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supfree (α ∧ β) with supfree α | supfree β
supfree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supfree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ∧ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∧ βpf n ⌈β⌉<n
supfree (α ∧ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ∧ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∧ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supfree (α ∨ β) with supfree α | supfree β
supfree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf with max ⌈α⌉ ⌈β⌉
supfree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , notFreeIs⌈β⌉
  where
    notFreeIs⌈β⌉ : ∀ n → ⌈β⌉ < n → mkvar n NotFreeIn (α ∨ β)
    notFreeIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∨ βpf n ⌈β⌉<n
supfree (α ∨ β) | ⌈α⌉ , αpf | ⌈β⌉ , βpf | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , notFreeIs⌈α⌉
  where
    notFreeIs⌈α⌉ : ∀ n → ⌈α⌉ < n → mkvar n NotFreeIn (α ∨ β)
    notFreeIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∨ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
supfree (Λ x α) with supfree α
supfree (Λ x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → Λ x (αpf n ⌈α⌉<n)
supfree (V x α) with supfree α
supfree (V x α) | ⌈α⌉ , αpf = ⌈α⌉ , λ n ⌈α⌉<n → V x (αpf n ⌈α⌉<n)


fresh : (α : Formula) → Σ Variable (_NotFreeIn α)
fresh α with supfree α
fresh α | s , ssup = mkvar (suc s) , ssup (suc s) ≤refl


record ReplacementVariable (α : Formula) (x : Variable) (t : Term) : Set where
  constructor freshvar
  field
    var         : Variable
    notFree     : var NotFreeIn α
    new         : x ≢ var
    replaceable : var NotFreeInTerm t


replacementvariable : ∀ α x t → ReplacementVariable α x t
replacementvariable α (mkvar n) t with supfree α | supfreeterm t
... | ⌈α⌉ , αpf | ⌈t⌉ , tpf with max n ⌈α⌉ | max n ⌈t⌉ | max ⌈α⌉ ⌈t⌉
...   | less n≤⌈α⌉ | less n≤⌈t⌉ | less ⌈α⌉≤⌈t⌉ = freshvar (mkvar (suc ⌈t⌉)) notFree new replaceable
  where
    notFree : mkvar (suc ⌈t⌉) NotFreeIn α
    notFree = αpf (suc ⌈t⌉) (sn≤sm ⌈α⌉≤⌈t⌉)
    new : mkvar n ≢ mkvar (suc ⌈t⌉)
    new refl = ⊥-elim (¬<refl n≤⌈t⌉)
    replaceable : mkvar (suc ⌈t⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈t⌉) (sn≤sm ≤refl)
...   | less n≤⌈α⌉ | less n≤⌈t⌉ | more ⌈t⌉≤⌈α⌉ = freshvar (mkvar (suc ⌈α⌉)) notFree new replaceable
  where
    notFree : mkvar (suc ⌈α⌉) NotFreeIn α
    notFree = αpf (suc ⌈α⌉) (sn≤sm ≤refl)
    new : mkvar n ≢ mkvar (suc ⌈α⌉)
    new refl = ¬<refl n≤⌈α⌉
    replaceable : mkvar (suc ⌈α⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈α⌉) (sn≤sm ⌈t⌉≤⌈α⌉)
...   | less n≤⌈α⌉ | more ⌈t⌉≤n | _            = freshvar (mkvar (suc ⌈α⌉)) notFree new replaceable
  where
    notFree : mkvar (suc ⌈α⌉) NotFreeIn α
    notFree = αpf (suc ⌈α⌉) (sn≤sm ≤refl)
    new : mkvar n ≢ mkvar (suc ⌈α⌉)
    new refl = ¬<refl n≤⌈α⌉
    replaceable : mkvar (suc ⌈α⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈α⌉) (≤trans (sn≤sm ⌈t⌉≤n) (sn≤sm n≤⌈α⌉))
...   | more ⌈α⌉≤n | less n≤⌈t⌉ | _            = freshvar (mkvar (suc ⌈t⌉)) notFree new replaceable
  where
    notFree : mkvar (suc ⌈t⌉) NotFreeIn α
    notFree = αpf (suc ⌈t⌉) (≤trans (sn≤sm ⌈α⌉≤n) (sn≤sm n≤⌈t⌉))
    new : mkvar n ≢ mkvar (suc ⌈t⌉)
    new refl = ¬<refl n≤⌈t⌉
    replaceable : mkvar (suc ⌈t⌉) NotFreeInTerm t
    replaceable = tpf (suc ⌈t⌉) (sn≤sm ≤refl)
...   | more ⌈α⌉≤n | more ⌈t⌉≤n | _            = freshvar (mkvar (suc n)) notFree new replaceable
  where
    notFree : mkvar (suc n) NotFreeIn α
    notFree = αpf (suc n) (sn≤sm ⌈α⌉≤n)
    new : mkvar n ≢ mkvar (suc n)
    new ()
    replaceable : mkvar (suc n) NotFreeInTerm t
    replaceable = tpf (suc n) (sn≤sm ⌈t⌉≤n)


-- Make sure to use the nicer substitutions for quantification where possible
_[_/_] : ∀ α x t → Σ Formula (α [ x / t ]≡_)
atom r us [ x / t ] = {!   !}
(α ⇒ β)   [ x / t ] with α [ x / t ] | β [ x / t ]
(α ⇒ β)   [ x / t ] | α′ , α[x/t]≡α′ | β′ , β[x/t]≡β′ = α′ ⇒ β′ , α[x/t]≡α′ ⇒ β[x/t]≡β′
(α ∧ β)   [ x / t ] with α [ x / t ] | β [ x / t ]
(α ∧ β)   [ x / t ] | α′ , α[x/t]≡α′ | β′ , β[x/t]≡β′ = α′ ∧ β′ , α[x/t]≡α′ ∧ β[x/t]≡β′
(α ∨ β)   [ x / t ] with α [ x / t ] | β [ x / t ]
(α ∨ β)   [ x / t ] | α′ , α[x/t]≡α′ | β′ , β[x/t]≡β′ = α′ ∨ β′ , α[x/t]≡α′ ∨ β[x/t]≡β′
Λ  y α    [ x / t ] with varEq x y | y notFreeInTerm t
Λ .x α    [ x / t ] | yes refl | _       = Λ x α , Λ∣ x α
Λ  y α    [ x / t ] | no x≢y   | yes xnf with α [ x / t ]
Λ  y α    [ x / t ] | no x≢y   | yes xnf | α′ , α[x/t]≡α′ = Λ y α′ , Λ x≢y xnf α[x/t]≡α′
Λ  y α    [ x / t ] | no x≢y   | no  xf  with replacementvariable α x t
Λ  y α    [ x / t ] | no x≢y   | no  xf  | freshvar ω ωnfα x≢ω ωnft with α [ y / varterm ω ]
Λ  y α    [ x / t ] | no x≢y   | no xf   | freshvar ω ωnfα x≢ω ωnft | β , α[y/ω]≡β with β [ x / t ]
Λ  y α    [ x / t ] | no x≢y   | no xf   | freshvar ω ωnfα x≢ω ωnft | β , α[y/ω]≡β | γ , β[x/t]≡γ = Λ ω γ , Λ/ ωnfα x≢ω ωnft α[y/ω]≡β β[x/t]≡γ
V y  α    [ x / t ] = {!   !}
