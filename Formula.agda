module Formula where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
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

infix 300 _BoundInTerm_ _BoundIn_ [_][_/_]≡_ _[_/_]≡_

data _BoundInTerm_ (x : Variable) : Term → Set where
  varterm  : ∀{y} → x ≢ y → x BoundInTerm (varterm y)
  functerm : ∀{f} {us : Vec Term (Function.arity f)}
               → All (x BoundInTerm_) us → x BoundInTerm (functerm f us)

data _BoundIn_ : Variable → Formula → Set where
  atom : ∀{x r} {ts : Vec Term (Relation.arity r)}
                  → All (x BoundInTerm_) ts → x BoundIn (atom r ts)
  _⇒_  : ∀{x α β} → x BoundIn α → x BoundIn β → x BoundIn (α ⇒ β)
  _∧_  : ∀{x α β} → x BoundIn α → x BoundIn β → x BoundIn (α ∧ β)
  _∨_  : ∀{x α β} → x BoundIn α → x BoundIn β → x BoundIn (α ∨ β)
  Λ∣   : ∀ x α    → x BoundIn Λ x α
  V∣   : ∀ x α    → x BoundIn V x α
  Λ    : ∀{x α}   → ∀ y → x BoundIn α → x BoundIn Λ y α
  V    : ∀{x α}   → ∀ y → x BoundIn α → x BoundIn V y α


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
  Λ     : ∀{α β x v t} → v ≢ x → x BoundInTerm t → α [ v / t ]≡ β → (Λ x α) [ v / t ]≡ (Λ x β)
  V     : ∀{α β x v t} → v ≢ x → x BoundInTerm t → α [ v / t ]≡ β → (V x α) [ v / t ]≡ (V x β)
  Λ/    : ∀{α β γ x v t ω} → ω BoundIn α → v ≢ ω → ω BoundInTerm t
          → α [ x / varterm ω ]≡ β → β [ v / t ]≡ γ → (Λ x α) [ v / t ]≡ (Λ ω γ)
  V/    : ∀{α β γ x v t ω} → ω BoundIn α → v ≢ ω → ω BoundInTerm t
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

≤refl : ∀{n} → n ≤ n
≤refl {zero}  = 0≤n
≤refl {suc n} = sn≤sm ≤refl

≤trans : ∀{x y z} → x ≤ y → y ≤ z → x ≤ z
≤trans 0≤n y≤z = 0≤n
≤trans (sn≤sm x≤y) (sn≤sm y≤z) = sn≤sm (≤trans x≤y y≤z)

_≤?_ : (n m : ℕ) → Dec (n ≤ m)
zero ≤? zero = yes 0≤n
zero ≤? suc m = yes 0≤n
suc n ≤? zero = no (λ ())
suc n ≤? suc m with n ≤? m
...            | yes n≤m = yes (sn≤sm n≤m)
...            | no ¬n≤m = no φ
                           where φ : _
                                 φ (sn≤sm n≤m) = ¬n≤m n≤m

order : ∀{n m} → ¬(n ≤ m) → m ≤ n
order {zero}  {m}     ¬n≤m = ⊥-elim (¬n≤m 0≤n)
order {suc n} {zero}  ¬n≤m = 0≤n
order {suc n} {suc m} ¬n≤m = sn≤sm (order (λ z → ¬n≤m (sn≤sm z)))

_boundInTerms_ : ∀{n} → (x : Variable) → (ts : Vec Term n) → Dec (All (x BoundInTerm_) ts)
x boundInTerms [] = yes []
x boundInTerms (t ∷ ts) with x boundInTerms ts
(x boundInTerms (t ∷ ts)) | no ¬rst = no φ
                                           where
                                             φ : ¬(All (x BoundInTerm_) (t ∷ ts))
                                             φ (_ ∷ rst) = ¬rst rst
(x boundInTerms (varterm y ∷ ts))     | yes rst with varEq x y
(x boundInTerms (varterm .x ∷ ts))    | yes rst | yes refl = no φ
                                                                  where
                                                                    φ : ¬(All (x BoundInTerm_) (varterm x ∷ ts))
                                                                    φ (varterm x≢x ∷ _) = x≢x refl
(x boundInTerms (varterm y ∷ ts))     | yes rst | no x≢y = yes (varterm x≢y ∷ rst)
(x boundInTerms (functerm f us ∷ ts)) | yes rst with x boundInTerms us
(x boundInTerms (functerm f us ∷ ts)) | yes rst | yes uspf = yes (functerm uspf ∷ rst)
(x boundInTerms (functerm f us ∷ ts)) | yes rst | no ¬uspf = no φ
                                                                  where
                                                                    φ : ¬(All (x BoundInTerm_) (functerm f us ∷ ts))
                                                                    φ (functerm uspf ∷ _) = ¬uspf uspf

_boundInTerm_ : (x : Variable) → (t : Term) → Dec (x BoundInTerm t)
x boundInTerm t with x boundInTerms (t ∷ [])
(x boundInTerm t) | yes (pf ∷ []) = yes pf
(x boundInTerm t) | no npf        = no λ z → npf (z ∷ [])

_boundIn_ : (x : Variable) → (α : Formula) → Dec (x BoundIn α)
x boundIn atom r ts with x boundInTerms ts
(x boundIn atom r ts) | yes bdts = yes (atom bdts)
(x boundIn atom r ts) | no ¬bdts = no φ
  where
    φ : ¬(x BoundIn atom r ts)
    φ (atom bdts) = ¬bdts bdts
x boundIn (α ⇒ β) with x boundIn α | x boundIn β
(x boundIn (α ⇒ β)) | yes αbd | yes βbd = yes (αbd ⇒ βbd)
(x boundIn (α ⇒ β)) | _       | no ¬βbd = no φ
                                          where
                                            φ : ¬(x BoundIn (α ⇒ β))
                                            φ (αbd ⇒ βbd) = ¬βbd βbd
(x boundIn (α ⇒ β)) | no ¬αbd | _       = no φ
                                          where
                                            φ : ¬(x BoundIn (α ⇒ β))
                                            φ (αbd ⇒ βbd) = ¬αbd αbd
x boundIn (α ∧ β) with x boundIn α | x boundIn β
(x boundIn (α ∧ β)) | yes αbd | yes βbd = yes (αbd ∧ βbd)
(x boundIn (α ∧ β)) | _       | no ¬βbd = no φ
                                          where
                                            φ : ¬(x BoundIn (α ∧ β))
                                            φ (αbd ∧ βbd) = ¬βbd βbd
(x boundIn (α ∧ β)) | no ¬αbd | _       = no φ
                                          where
                                            φ : ¬(x BoundIn (α ∧ β))
                                            φ (αbd ∧ βbd) = ¬αbd αbd
x boundIn (α ∨ β) with x boundIn α | x boundIn β
(x boundIn (α ∨ β)) | yes αbd | yes βbd = yes (αbd ∨ βbd)
(x boundIn (α ∨ β)) | _       | no ¬βbd = no φ
                                          where
                                            φ : ¬(x BoundIn (α ∨ β))
                                            φ (αbd ∨ βbd) = ¬βbd βbd
(x boundIn (α ∨ β)) | no ¬αbd | _       = no φ
                                          where
                                            φ : ¬(x BoundIn (α ∨ β))
                                            φ (αbd ∨ βbd) = ¬αbd αbd
x boundIn Λ y α with varEq x y
(x boundIn Λ .x α) | yes refl = yes (Λ∣ x α)
(x boundIn Λ y α)  | no x≢y with x boundIn α
(x boundIn Λ y α) | no x≢y | yes αbd = yes (Λ y αbd)
(x boundIn Λ y α) | no x≢y | no ¬αbd = no φ
                                       where
                                         φ : ¬(x BoundIn Λ y α)
                                         φ (Λ∣ x α) = x≢y refl
                                         φ (Λ y αbd) = ¬αbd αbd
x boundIn V y α with varEq x y
(x boundIn V .x α) | yes refl = yes (V∣ x α)
(x boundIn V y α)  | no x≢y with x boundIn α
(x boundIn V y α) | no x≢y | yes αbd = yes (V y αbd)
(x boundIn V y α) | no x≢y | no ¬αbd = no φ
                                       where
                                         φ : ¬(x BoundIn V y α)
                                         φ (V∣ x α) = x≢y refl
                                         φ (V y αbd) = ¬αbd αbd


greatestvar : ∀{k} → (ts : Vec Term k) → Σ ℕ (λ n → ∀ m → ¬(All (mkvar m BoundInTerm_) ts) → m ≤ n)
greatestvar [] = zero , λ m ¬[]dno → ⊥-elim (¬[]dno [])
greatestvar (x ∷ ts) with greatestvar ts
greatestvar (varterm (mkvar n) ∷ ts) | gts , gtspf with n ≤? gts
greatestvar (varterm (mkvar n) ∷ ts) | gts , gtspf | yes n≤gts = gts , φ
  where
    φ : ∀ m → ¬(All (mkvar m BoundInTerm_) (varterm (mkvar n) ∷ ts)) → m ≤ gts
    φ m ¬all with mkvar m boundInTerm (varterm (mkvar n))
    φ m ¬all | yes (varterm m≢n) = gtspf m λ rst → ¬all (varterm m≢n ∷ rst)
    φ m ¬all | no ¬head with varEq (mkvar m) (mkvar n)
    φ m ¬all | no ¬head | yes refl = n≤gts
    φ m ¬all | no ¬head | no x = ⊥-elim (¬head (varterm x))
greatestvar (varterm (mkvar n) ∷ ts) | gts , gtspf | no ¬n≤gts = n , φ
  where
    φ : ∀ m → ¬(All (mkvar m BoundInTerm_) (varterm (mkvar n) ∷ ts)) → m ≤ n
    φ m ¬all with mkvar m boundInTerm (varterm (mkvar n))
    φ m ¬all | yes (varterm x) = ≤trans (gtspf m (λ z → ¬all (varterm x ∷ z))) (order ¬n≤gts)
    φ m ¬all | no ¬head with varEq (mkvar m) (mkvar n)
    φ m ¬all | no ¬head | yes refl = ≤refl
    φ m ¬all | no ¬head | no x = ⊥-elim (¬head (varterm x))
greatestvar (functerm f us ∷ ts) | gts , gtspf with greatestvar us
greatestvar (functerm f us ∷ ts) | gts , gtspf | gus , guspf with gus ≤? gts
greatestvar (functerm f us ∷ ts) | gts , gtspf | gus , guspf | yes gus≤gts = gts , φ
  where
    φ : ∀ m → ¬ All (mkvar m BoundInTerm_) (functerm f us ∷ ts) → m ≤ gts
    φ m ¬all with mkvar m boundInTerm (functerm f us)
    φ m ¬all | yes (functerm x) = gtspf m λ z → ¬all (functerm x ∷ z)
    φ m ¬all | no ¬head = ≤trans (guspf m (λ z → ¬head (functerm z))) gus≤gts
greatestvar (functerm f us ∷ ts) | gts , gtspf | gus , guspf | no ¬gus≤gts = gus , φ
  where
    φ : ∀ m → ¬ All (mkvar m BoundInTerm_) (functerm f us ∷ ts) → m ≤ gus
    φ m ¬all with mkvar m boundInTerm (functerm f us)
    φ m ¬all | yes (functerm x) = ≤trans (gtspf m (λ z → ¬all (functerm x ∷ z))) (order ¬gus≤gts)
    φ m ¬all | no ¬head = guspf m λ z → ¬head (functerm z)

-- No guarantee that this bound is tight - in fact for the V and Λ cases it is
-- not tight if the quantifier is the greatest variable (and does not have index
-- zero)
greatest : (α : Formula) → Σ ℕ (λ n → ∀ m → ¬((mkvar m) BoundIn α) → m ≤ n)
greatest (atom r ts) with greatestvar ts
greatest (atom r ts) | gts , gtspf = gts , λ m ¬tsbd → gtspf m (λ tsdno → ¬tsbd (atom tsdno))
greatest (α ⇒ β) with greatest α | greatest β
greatest (α ⇒ β) | gα , gαpf | gβ , gβpf with gα ≤? gβ
greatest (α ⇒ β) | gα , gαpf | gβ , gβpf | yes gα≤gβ = gβ , φ
  where
    φ : (n : ℕ) → ¬(mkvar n BoundIn (α ⇒ β)) → n ≤ gβ
    φ n ¬bd with mkvar n boundIn α | mkvar n boundIn β
    φ n ¬bd | yes αbd | yes βbd = ⊥-elim (¬bd (αbd ⇒ βbd))
    φ n ¬bd | _       | no ¬βbd = gβpf n ¬βbd
    φ n ¬bd | no ¬αbd | _       = ≤trans (gαpf n ¬αbd) gα≤gβ
greatest (α ⇒ β) | gα , gαpf | gβ , gβpf | no ¬gα≤gβ = gα , φ
  where
    φ : (n : ℕ) → ¬(mkvar n BoundIn (α ⇒ β)) → n ≤ gα
    φ n ¬bd with mkvar n boundIn β | mkvar n boundIn α
    φ n ¬bd | yes βbd | yes αbd = ⊥-elim (¬bd (αbd ⇒ βbd))
    φ n ¬bd | _       | no ¬αbd = gαpf n ¬αbd
    φ n ¬bd | no ¬βbd | _       = ≤trans (gβpf n ¬βbd) (order ¬gα≤gβ)
greatest (α ∧ β) with greatest α | greatest β
greatest (α ∧ β) | gα , gαpf | gβ , gβpf with gα ≤? gβ
greatest (α ∧ β) | gα , gαpf | gβ , gβpf | yes gα≤gβ = gβ , φ
  where
    φ : (n : ℕ) → ¬(mkvar n BoundIn (α ∧ β)) → n ≤ gβ
    φ n ¬bd with mkvar n boundIn α | mkvar n boundIn β
    φ n ¬bd | yes αbd | yes βbd = ⊥-elim (¬bd (αbd ∧ βbd))
    φ n ¬bd | _       | no ¬βbd = gβpf n ¬βbd
    φ n ¬bd | no ¬αbd | _       = ≤trans (gαpf n ¬αbd) gα≤gβ
greatest (α ∧ β) | gα , gαpf | gβ , gβpf | no ¬gα≤gβ = gα , φ
  where
    φ : (n : ℕ) → ¬(mkvar n BoundIn (α ∧ β)) → n ≤ gα
    φ n ¬bd with mkvar n boundIn β | mkvar n boundIn α
    φ n ¬bd | yes βbd | yes αbd = ⊥-elim (¬bd (αbd ∧ βbd))
    φ n ¬bd | _       | no ¬αbd = gαpf n ¬αbd
    φ n ¬bd | no ¬βbd | _       = ≤trans (gβpf n ¬βbd) (order ¬gα≤gβ)
greatest (α ∨ β) with greatest α | greatest β
greatest (α ∨ β) | gα , gαpf | gβ , gβpf with gα ≤? gβ
greatest (α ∨ β) | gα , gαpf | gβ , gβpf | yes gα≤gβ = gβ , φ
  where
    φ : (n : ℕ) → ¬(mkvar n BoundIn (α ∨ β)) → n ≤ gβ
    φ n ¬bd with mkvar n boundIn α | mkvar n boundIn β
    φ n ¬bd | yes αbd | yes βbd = ⊥-elim (¬bd (αbd ∨ βbd))
    φ n ¬bd | _       | no ¬βbd = gβpf n ¬βbd
    φ n ¬bd | no ¬αbd | _       = ≤trans (gαpf n ¬αbd) gα≤gβ
greatest (α ∨ β) | gα , gαpf | gβ , gβpf | no ¬gα≤gβ = gα , φ
  where
    φ : (n : ℕ) → ¬(mkvar n BoundIn (α ∨ β)) → n ≤ gα
    φ n ¬bd with mkvar n boundIn β | mkvar n boundIn α
    φ n ¬bd | yes βbd | yes αbd = ⊥-elim (¬bd (αbd ∨ βbd))
    φ n ¬bd | _       | no ¬αbd = gαpf n ¬αbd
    φ n ¬bd | no ¬βbd | _       = ≤trans (gβpf n ¬βbd) (order ¬gα≤gβ)
greatest (Λ x α) with greatest α
greatest (Λ x α) | gα , gαpf = gα , λ m ¬mbd → gαpf m (λ β → ¬mbd (Λ x β))
greatest (V x α) with greatest α
greatest (V x α) | gα , gαpf = gα , λ m ¬mbd → gαpf m (λ β → ¬mbd (V x β))

fresh : (α : Formula) → Σ Variable (_BoundIn α)
fresh α with greatest α
fresh α | gα , gαpf = mkvar (suc gα) , stab λ φ → ¬sn≤n (gαpf (suc gα) φ)
  where
    ¬sn≤n : ∀{n} → ¬(suc n ≤ n)
    ¬sn≤n {zero}  ()
    ¬sn≤n {suc n} (sn≤sm pf) = ¬sn≤n pf
    stab : ∀{α x} → ¬ ¬(x BoundIn α) → x BoundIn α
    stab {α} {x} ¬¬bd with x boundIn α
    stab {α} {x} ¬¬bd | yes bd = bd
    stab {α} {x} ¬¬bd | no ¬bd = ⊥-elim (¬¬bd ¬bd)

