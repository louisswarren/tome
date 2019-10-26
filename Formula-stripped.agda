


open import Agda.Builtin.Sigma


open import Decidable
open import Nat
open import Vec


record Variable : Set where
  constructor var
  field
    index : ℕ

open Variable renaming (index to varidx)

record Function : Set where
  constructor func
  field
    index : ℕ
    arity : ℕ

open Function renaming (index to funcidx ; arity to funcarity)


data Term : Set where
  varterm  : Variable → Term
  functerm : (f : Function) → Vec Term (funcarity f) → Term


record Relation : Set where
  constructor rel
  field
    idx   : ℕ
    arity : ℕ

open Relation renaming (idx to relidx ; arity to relarity)


data Formula : Set where
  atom   : (r : Relation) → Vec Term (relarity r) → Formula
  _⇒_    : Formula  → Formula → Formula
  _∧_    : Formula  → Formula → Formula
  _∨_    : Formula  → Formula → Formula
  Λ      : Variable → Formula → Formula
  V      : Variable → Formula → Formula

_⇔_ : Formula → Formula → Formula
Φ ⇔ Ψ = (Φ ⇒ Ψ) ∧ (Ψ ⇒ Φ)


infixr 105 _⇒_ _⇔_
infixr 106 _∨_
infixr 107 _∧_


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


vecEq : ∀{n} {A : Set} → Decidable≡ A → Decidable≡ (Vec A n)
vecEq eq [] [] = yes refl
vecEq eq (x ∷ xs) (y ∷ ys) with eq x y
...                        | no  x≢y  = no λ { refl → x≢y refl }
...                        | yes refl with vecEq eq xs ys
...                                   | yes refl  = yes refl
...                                   | no  xs≢xy = no λ { refl → xs≢xy refl }


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


data _NotInTerm_ (x : Variable) : Term → Set

_NotInTerms_ : ∀{n} → Variable → Vec Term n → Set
x NotInTerms ts = All (x NotInTerm_) ts

data _NotInTerm_ x where
  varterm  : ∀{y} → x ≢ y → x NotInTerm (varterm y)
  functerm : ∀{f} {us : Vec Term (funcarity f)}
                  → x NotInTerms us → x NotInTerm (functerm f us)


data _NotFreeIn_ : Variable → Formula → Set where
  atom : ∀{x r} {ts : Vec Term (relarity r)}
                  → x NotInTerms ts → x NotFreeIn (atom r ts)
  _⇒_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ⇒ β)
  _∧_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ∧ β)
  _∨_  : ∀{x α β} → x NotFreeIn α → x NotFreeIn β → x NotFreeIn (α ∨ β)
  Λ↓   : ∀ x α    → x NotFreeIn Λ x α
  V↓   : ∀ x α    → x NotFreeIn V x α
  Λ    : ∀{x α}   → ∀ y → x NotFreeIn α → x NotFreeIn Λ y α
  V    : ∀{x α}   → ∀ y → x NotFreeIn α → x NotFreeIn V y α


_notInTerms_ : ∀{n} → ∀ x → (ts : Vec Term n) → Dec (x NotInTerms ts)
x notInTerms [] = yes []
x notInTerms (varterm y ∷ ts) with varEq x y
...    | yes refl = no λ { (varterm x≢x ∷ _) → x≢x refl }
...    | no  x≢y  with x notInTerms ts
...               | yes x∉ts = yes (varterm x≢y ∷ x∉ts)
...               | no ¬x∉ts = no  λ { (_ ∷ x∉ts) → ¬x∉ts x∉ts }
x notInTerms (functerm f us ∷ ts) with x notInTerms us
...    | no ¬x∉us = no λ { (functerm x∉us ∷ _) → ¬x∉us x∉us }
...    | yes x∉us with x notInTerms ts
...               | yes x∉ts = yes (functerm x∉us ∷ x∉ts)
...               | no ¬x∉ts = no  λ { (_ ∷ x∉ts) → ¬x∉ts x∉ts }


_notInTerm_ : (x : Variable) → (t : Term) → Dec (x NotInTerm t)
x notInTerm varterm y     with varEq x y
...                       | yes refl = no  λ { (varterm x≢x) → x≢x refl }
...                       | no  x≢y  = yes (varterm x≢y)
x notInTerm functerm f ts with x notInTerms ts
...                       | yes x∉ts = yes (functerm x∉ts)
...                       | no ¬x∉ts = no  λ { (functerm x∉ts) → ¬x∉ts x∉ts }


_notFreeIn_ : (x : Variable) → (α : Formula) → Dec (x NotFreeIn α)
x notFreeIn atom r ts with x notInTerms ts
...                   | yes x∉ts = yes (atom x∉ts)
...                   | no ¬x∉ts = no  λ { (atom x∉ts) → ¬x∉ts x∉ts }
x notFreeIn (α ⇒ β)   with x notFreeIn α | x notFreeIn β
...                   | yes x∉α | yes x∉β = yes (x∉α ⇒ x∉β)
...                   | no ¬x∉α | _       = no  λ { (x∉α ⇒ _  ) → ¬x∉α x∉α }
...                   | _       | no ¬x∉β = no  λ { (_   ⇒ x∉β) → ¬x∉β x∉β }
x notFreeIn (α ∧ β)   with x notFreeIn α | x notFreeIn β
...                   | yes x∉α | yes x∉β = yes (x∉α ∧ x∉β)
...                   | no ¬x∉α | _       = no  λ { (x∉α ∧ _  ) → ¬x∉α x∉α }
...                   | _       | no ¬x∉β = no  λ { (_   ∧ x∉β) → ¬x∉β x∉β }
x notFreeIn (α ∨ β)   with x notFreeIn α | x notFreeIn β
...                   | yes x∉α | yes x∉β = yes (x∉α ∨ x∉β)
...                   | no ¬x∉α | _       = no  λ { (x∉α ∨ _  ) → ¬x∉α x∉α }
...                   | _       | no ¬x∉β = no  λ { (_   ∨ x∉β) → ¬x∉β x∉β }
x notFreeIn Λ  y α    with varEq x y
...                   | yes refl = yes (Λ↓ x α)
...                   | no  x≢y  with x notFreeIn α
...                              | yes x∉α = yes (Λ y x∉α)
...                              | no ¬x∉α = no  λ { (Λ↓ x α)  → x≢y refl
                                                   ; (Λ y x∉α) → ¬x∉α x∉α }
x notFreeIn V  y α    with varEq x y
...                   | yes refl = yes (V↓ x α)
...                   | no  x≢y  with x notFreeIn α
...                              | yes x∉α = yes (V y x∉α)
...                              | no ¬x∉α = no  λ { (V↓ x α)  → x≢y refl
                                                   ; (V y x∉α) → ¬x∉α x∉α }







































--subIdentFunc : ∀{α x β} → α [ x / varterm x ]≡ β → α ≡ β
--
--
--subIdentFunc (ident α x) = refl
--subIdentFunc (notfree x) = refl
--subIdentFunc (atom r ts) = vecEq→Eq (termsLemma ts)
--  where
--    vecEq→Eq : {us vs : Vec Term (relarity r)}
--               → us ≡ vs → atom r us ≡ atom r vs
--    vecEq→Eq refl = refl
--    termsLemma : ∀{n x} {us vs : Vec Term n}
--                   → [ us ][ x / varterm x ]≡ vs → us ≡ vs
--    termsLemma []                  = refl
--    termsLemma (r            ∷ rs) with termsLemma rs
--    termsLemma (varterm≡     ∷ rs) | refl = refl
--    termsLemma (varterm≢ x≢y ∷ rs) | refl = refl
--    termsLemma (functerm ts  ∷ rs) | refl rewrite termsLemma ts = refl
--subIdentFunc (subα ⇒ subβ) with subIdentFunc subα | subIdentFunc subβ
--...                   | refl | refl = refl
--subIdentFunc (subα ∧ subβ) with subIdentFunc subα | subIdentFunc subβ
--...                   | refl | refl = refl
--subIdentFunc (subα ∨ subβ) with subIdentFunc subα | subIdentFunc subβ
--...                   | refl | refl = refl
--subIdentFunc (Λ↓ x α) = refl
--subIdentFunc (V↓ x α) = refl
--subIdentFunc (Λ x≢y y∉x sub) rewrite subIdentFunc sub = refl
--subIdentFunc (V x≢y y∉x sub) rewrite subIdentFunc sub = refl
--
--subNotFreeFunc : ∀{α x t β} → α [ x / t ]≡ β → x NotFreeIn α → α ≡ β
--
--
--subNotFreeFunc (ident α x) x∉α = refl
--subNotFreeFunc (notfree x) x∉α = refl
--subNotFreeFunc (atom p r) (atom x∉xs) = vecEq→Eq (termsLemma r x∉xs)
--  where
--    vecEq→Eq : {us vs : Vec Term (relarity p)}
--               → us ≡ vs → atom p us ≡ atom p vs
--    vecEq→Eq refl = refl
--    termsLemma : ∀{n x t} {us vs : Vec Term n}
--                  → [ us ][ x / t ]≡ vs → x NotInTerms us → us ≡ vs
--    termsLemma [] x∉us = refl
--    termsLemma (r ∷ rs) (x∉u ∷ x∉us) with termsLemma rs x∉us
--    termsLemma (varterm≡     ∷ rs) (varterm x≢x   ∷ x∉us) | refl = ⊥-elim (x≢x refl)
--    termsLemma (varterm≢ x≢y ∷ rs) (x∉u           ∷ x∉us) | refl = refl
--    termsLemma (functerm rt  ∷ rs) (functerm x∉ts ∷ x∉us) | refl
--               rewrite termsLemma rt x∉ts = refl
--subNotFreeFunc (subα ⇒ subβ) (x∉α ⇒ x∉β) with subNotFreeFunc subα x∉α | subNotFreeFunc subβ x∉β
--...                                 | refl | refl = refl
--subNotFreeFunc (subα ∧ subβ) (x∉α ∧ x∉β) with subNotFreeFunc subα x∉α | subNotFreeFunc subβ x∉β
--...                                 | refl | refl = refl
--subNotFreeFunc (subα ∨ subβ) (x∉α ∨ x∉β) with subNotFreeFunc subα x∉α | subNotFreeFunc subβ x∉β
--...                                 | refl | refl = refl
--subNotFreeFunc (Λ↓ x α) _ = refl
--subNotFreeFunc (V↓ x α) _ = refl
--subNotFreeFunc (Λ x≢x _ r) (Λ↓ x α) = ⊥-elim (x≢x refl)
--subNotFreeFunc (Λ x≢y _ r) (Λ y x∉α) rewrite subNotFreeFunc r x∉α = refl
--subNotFreeFunc (V x≢y _ r) (V↓ x α) = ⊥-elim (x≢y refl)
--subNotFreeFunc (V x≢y _ r) (V y x∉α) rewrite subNotFreeFunc r x∉α = refl
--
--
--subTermsFunc : ∀{n x t} {us vs ws : Vec Term n}
--               → [ us ][ x / t ]≡ vs → [ us ][ x / t ]≡ ws → vs ≡ ws
--subTermsFunc [] [] = refl
--subTermsFunc (s ∷ ss) (r ∷ rs) with subTermsFunc ss rs
--subTermsFunc (varterm≡     ∷ _) (varterm≡     ∷ _) | refl = refl
--subTermsFunc (varterm≡     ∷ _) (varterm≢ x≢x ∷ _) | refl = ⊥-elim (x≢x refl)
--subTermsFunc (varterm≢ x≢x ∷ _) (varterm≡     ∷ _) | refl = ⊥-elim (x≢x refl)
--subTermsFunc (varterm≢ x≢y ∷ _) (varterm≢ _   ∷ _) | refl = refl
--subTermsFunc (functerm st  ∷ _) (functerm rt  ∷ _)
--             | refl rewrite subTermsFunc st rt = refl
--
--
--subFunc : ∀{x t α β γ} → α [ x / t ]≡ β → α [ x / t ]≡ γ → β ≡ γ
--subFunc (ident α x)   s             = subIdentFunc s
--subFunc (notfree x∉α) s             = subNotFreeFunc s x∉α
--subFunc r             (ident α x)   rewrite subIdentFunc r       = refl
--subFunc r             (notfree x∉α) rewrite subNotFreeFunc r x∉α = refl
--subFunc (atom p r)    (atom .p s)   rewrite subTermsFunc r s = refl
--subFunc (r₁ ⇒ r₂)     (s₁ ⇒ s₂)     with subFunc r₁ s₁ | subFunc r₂ s₂
--...                                 | refl | refl = refl
--subFunc (r₁ ∧ r₂)     (s₁ ∧ s₂)     with subFunc r₁ s₁ | subFunc r₂ s₂
--...                                 | refl | refl = refl
--subFunc (r₁ ∨ r₂)     (s₁ ∨ s₂)     with subFunc r₁ s₁ | subFunc r₂ s₂
--...                                 | refl | refl = refl
--subFunc (Λ↓ x α)      (Λ↓ .x .α)    = refl
--subFunc (V↓ x α)      (V↓ .x .α)    = refl
--subFunc (Λ↓ x α)      (Λ x≢x _ s)   = ⊥-elim (x≢x refl)
--subFunc (V↓ x α)      (V x≢x _ s)   = ⊥-elim (x≢x refl)
--subFunc (Λ x≢x _ r)   (Λ↓ x α)      = ⊥-elim (x≢x refl)
--subFunc (V x≢x _ r)   (V↓ x α)      = ⊥-elim (x≢x refl)
--subFunc (Λ _ _ r)     (Λ _ _ s)     rewrite subFunc r s = refl
--subFunc (V _ _ r)     (V _ _ s)     rewrite subFunc r s = refl


data _FreeFor_In_ (t : Term) (x : Variable) : Formula → Set where
  notfree : ∀{α} → x NotFreeIn α → t FreeFor x In α
  atom    : ∀ r us → t FreeFor x In atom r us
  _⇒_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β
                     → t FreeFor x In α ⇒ β
  _∧_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β
                     → t FreeFor x In α ∧ β
  _∨_     : ∀{α β} → t FreeFor x In α → t FreeFor x In β
                     → t FreeFor x In α ∨ β
  Λ↓      : ∀ α → t FreeFor x In Λ x α
  V↓      : ∀ α → t FreeFor x In V x α
  Λ       : ∀{α y} → y NotInTerm t → t FreeFor x In α → t FreeFor x In Λ y α
  V       : ∀{α y} → y NotInTerm t → t FreeFor x In α → t FreeFor x In V y α

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
    ...                  | yes refl = yes (Λ↓ α)
    ...                  | no  x≢y  with t freeFor x In α
    ...                             | no ¬tffα = no ¬tff
                                                 where
                                                   ¬tff : _
                                                   ¬tff (notfree xnf) = xf xnf
                                                   ¬tff (Λ↓ .α) = x≢y refl
                                                   ¬tff (Λ _ tffα) = ¬tffα tffα
    ...                             | yes tffα with y notInTerm t
    ...                                        | yes ynft = yes (Λ ynft tffα)
    ...                                        | no ¬ynft = no ¬tff
                                                            where
                                                              ¬tff : _
                                                              ¬tff (notfree xnf) = xf xnf
                                                              ¬tff (Λ↓ .α) = x≢y refl
                                                              ¬tff (Λ ynft _) = ¬ynft ynft
    lemma (V y α)     xf with varEq x y
    ...                  | yes refl = yes (V↓ α)
    ...                  | no  x≢y  with t freeFor x In α
    ...                             | no ¬tffα = no ¬tff
                                                 where
                                                   ¬tff : _
                                                   ¬tff (notfree xnf) = xf xnf
                                                   ¬tff (V↓ .α) = x≢y refl
                                                   ¬tff (V _ tffα) = ¬tffα tffα
    ...                             | yes tffα with y notInTerm t
    ...                                        | yes ynft = yes (V ynft tffα)
    ...                                        | no ¬ynft = no ¬tff
                                                            where
                                                              ¬tff : _
                                                              ¬tff (notfree xnf) = xf xnf
                                                              ¬tff (V↓ .α) = x≢y refl
                                                              ¬tff (V ynft _) = ¬ynft ynft

data _FreshIn_ (x : Variable) : Formula → Set where
  atom : ∀{r ts} → x NotInTerms ts → x FreshIn (atom r ts)
  _⇒_  : ∀{α β}  → x FreshIn α → x FreshIn β → x FreshIn α ⇒ β
  _∧_  : ∀{α β}  → x FreshIn α → x FreshIn β → x FreshIn α ∧ β
  _∨_  : ∀{α β}  → x FreshIn α → x FreshIn β → x FreshIn α ∨ β
  Λ    : ∀{α y}  → y ≢ x → x FreshIn α → x FreshIn Λ y α
  V    : ∀{α y}  → y ≢ x → x FreshIn α → x FreshIn V y α


freshNotFree : ∀{α x} → x FreshIn α → x NotFreeIn α


freshNotFree (atom x∉ts)   = atom x∉ts
freshNotFree (xfrα ⇒ xfrβ) = freshNotFree xfrα ⇒ freshNotFree xfrβ
freshNotFree (xfrα ∧ xfrβ) = freshNotFree xfrα ∧ freshNotFree xfrβ
freshNotFree (xfrα ∨ xfrβ) = freshNotFree xfrα ∨ freshNotFree xfrβ
freshNotFree (Λ _ xfrα)    = Λ _ (freshNotFree xfrα)
freshNotFree (V _ xfrα)    = V _ (freshNotFree xfrα)


freshFreeFor : ∀{α x} → x FreshIn α → ∀ y → (varterm x) FreeFor y In α


freshFreeFor (atom _)      y = atom _ _
freshFreeFor (xfrα ⇒ xfrβ) y = freshFreeFor xfrα y ⇒ freshFreeFor xfrβ y
freshFreeFor (xfrα ∧ xfrβ) y = freshFreeFor xfrα y ∧ freshFreeFor xfrβ y
freshFreeFor (xfrα ∨ xfrβ) y = freshFreeFor xfrα y ∨ freshFreeFor xfrβ y
freshFreeFor (Λ x≢y xfrα)  y = Λ (varterm x≢y) (freshFreeFor xfrα y)
freshFreeFor (V x≢y xfrα)  y = V (varterm x≢y) (freshFreeFor xfrα y)


maxVarTerms : ∀{k} → (ts : Vec Term k)
              → Σ Variable (λ ⌈ts⌉
                            → ∀ n → varidx ⌈ts⌉ < n → var n NotInTerms ts)
maxVarTerms []                   = var zero , (λ _ _ → [])
maxVarTerms (varterm x     ∷ ts) with maxVarTerms ts
... | ⌈ts⌉ , tspf with compare (varidx x) (varidx ⌈ts⌉)
...               | more ⌈ts⌉≤x = x , maxIsx
  where
    maxIsx : ∀ n → (varidx x) < n → (var n) NotInTerms (varterm x ∷ ts)
    maxIsx n x<n    = varterm (λ { refl → ℕdisorder x<n ≤refl })
                      ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤x) x<n)
...               | less x≤⌈ts⌉ = ⌈ts⌉ , ⌈ts⌉pf
  where
    ⌈ts⌉pf : ∀ n → varidx ⌈ts⌉ < n → var n NotInTerms (varterm x ∷ ts)
    ⌈ts⌉pf n ⌈ts⌉<n = varterm (λ { refl → ℕdisorder ⌈ts⌉<n x≤⌈ts⌉ })
                      ∷ tspf n ⌈ts⌉<n
maxVarTerms (functerm f us ∷ ts) with maxVarTerms us | maxVarTerms ts
... | ⌈us⌉ , uspf | ⌈ts⌉ , tspf with compare (varidx ⌈us⌉) (varidx ⌈ts⌉)
...                             | more ⌈ts⌉≤⌈us⌉ = ⌈us⌉ , ⌈us⌉pf
  where
    ⌈us⌉pf : ∀ n → varidx ⌈us⌉ < n → (var n) NotInTerms (functerm f us ∷ ts)
    ⌈us⌉pf n ⌈us⌉<n = functerm (uspf n ⌈us⌉<n)
                      ∷ tspf n (≤trans (sn≤sm ⌈ts⌉≤⌈us⌉) ⌈us⌉<n)
...                             | less ⌈us⌉≤⌈ts⌉ = ⌈ts⌉ , ⌈ts⌉pf
  where
    ⌈ts⌉pf : ∀ n → varidx ⌈ts⌉ < n → (var n) NotInTerms (functerm f us ∷ ts)
    ⌈ts⌉pf n ⌈ts⌉<n = functerm (uspf n (≤trans (sn≤sm ⌈us⌉≤⌈ts⌉) ⌈ts⌉<n))
                      ∷ tspf n ⌈ts⌉<n

maxVar : ∀ α → Σ Variable λ ⌈α⌉ → ∀ n → varidx ⌈α⌉ < n → var n FreshIn α
maxVar (atom r ts) with maxVarTerms ts
...                  | ⌈ts⌉ , tspf = ⌈ts⌉ , λ n ⌈ts⌉<n → atom (tspf n ⌈ts⌉<n)
maxVar (α ⇒ β) with maxVar α | maxVar β
...    | ⌈α⌉ , αpf | ⌈β⌉ , βpf with compare (varidx ⌈α⌉) (varidx ⌈β⌉)
...                            | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , maxIs⌈β⌉
    where
      maxIs⌈β⌉ : ∀ n → varidx ⌈β⌉ < n → var n FreshIn (α ⇒ β)
      maxIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ⇒ βpf n ⌈β⌉<n
...                            | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
    where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn (α ⇒ β)
      maxIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ⇒ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
maxVar (α ∧ β) with maxVar α | maxVar β
...    | ⌈α⌉ , αpf | ⌈β⌉ , βpf with compare (varidx ⌈α⌉) (varidx ⌈β⌉)
...                            | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , maxIs⌈β⌉
    where
      maxIs⌈β⌉ : ∀ n → varidx ⌈β⌉ < n → var n FreshIn (α ∧ β)
      maxIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∧ βpf n ⌈β⌉<n
...                            | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
    where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn (α ∧ β)
      maxIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∧ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
maxVar (α ∨ β) with maxVar α | maxVar β
...    | ⌈α⌉ , αpf | ⌈β⌉ , βpf with compare (varidx ⌈α⌉) (varidx ⌈β⌉)
...                            | less ⌈α⌉≤⌈β⌉ = ⌈β⌉ , maxIs⌈β⌉
    where
      maxIs⌈β⌉ : ∀ n → varidx ⌈β⌉ < n → var n FreshIn (α ∨ β)
      maxIs⌈β⌉ n ⌈β⌉<n = αpf n (≤trans (sn≤sm ⌈α⌉≤⌈β⌉) ⌈β⌉<n) ∨ βpf n ⌈β⌉<n
...                            | more ⌈β⌉≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
    where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn (α ∨ β)
      maxIs⌈α⌉ n ⌈α⌉<n = αpf n ⌈α⌉<n ∨ βpf n (≤trans (sn≤sm ⌈β⌉≤⌈α⌉) ⌈α⌉<n)
maxVar (Λ x α) with maxVar α
...              | ⌈α⌉ , αpf with compare (varidx x) (varidx ⌈α⌉)
...                          | less x≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
  where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn Λ x α
      maxIs⌈α⌉ n ⌈α⌉<n = Λ (λ { refl → ℕdisorder ⌈α⌉<n x≤⌈α⌉ }) (αpf n ⌈α⌉<n)
...                          | more ⌈α⌉≤x = x , maxIsx
  where
      maxIsx : ∀ n → varidx x < n → var n FreshIn Λ x α
      maxIsx n x<n = Λ (λ { refl → ℕdisorder x<n ≤refl })
                        (αpf n (≤trans (sn≤sm ⌈α⌉≤x) x<n))
maxVar (V x α) with maxVar α
...              | ⌈α⌉ , αpf with compare (varidx x) (varidx ⌈α⌉)
...                          | less x≤⌈α⌉ = ⌈α⌉ , maxIs⌈α⌉
  where
      maxIs⌈α⌉ : ∀ n → varidx ⌈α⌉ < n → var n FreshIn V x α
      maxIs⌈α⌉ n ⌈α⌉<n = V (λ { refl → ℕdisorder ⌈α⌉<n x≤⌈α⌉ }) (αpf n ⌈α⌉<n)
...                          | more ⌈α⌉≤x = x , maxIsx
  where
      maxIsx : ∀ n → varidx x < n → var n FreshIn V x α
      maxIsx n x<n = V (λ { refl → ℕdisorder x<n ≤refl })
                        (αpf n (≤trans (sn≤sm ⌈α⌉≤x) x<n))

fresh : ∀ α → Σ Variable (_FreshIn α)
fresh α with maxVar α
...     | ⌈α⌉ , αpf = var (suc (varidx ⌈α⌉)) , αpf (suc (varidx ⌈α⌉)) ≤refl


{-
  record Σ (A : Set) (B : A → Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst
-}


[_][_/_] : ∀{n} → Vec Term n → Variable → Term → Vec Term n
[ []                 ][ x / t ] = []
[ varterm y     ∷ us ][ x / t ] with varEq x y
...                             | yes _ = t         ∷ [ us ][ x / t ]
...                             | no  _ = varterm y ∷ [ us ][ x / t ]
[ functerm f ws ∷ us ][ x / t ] = functerm f [ ws ][ x / t ] ∷ [ us ][ x / t ]


_[_/_] : ∀{t} → Formula → Variable → Term → Formula
(atom r ts) [ x / t ]  = atom r [ ts ][ x / t ]
(α ⇒ β) [ x / t ]  = (α [ x / t ]) ⇒ (β [ x / t ])
(α ∧ β) [ x / t ]  = (α [ x / t ]) ∧ (β [ x / t ])
(α ∨ β) [ x / t ]  = (α [ x / t ]) ∨ (β [ x / t ])
Λ y α   [ x / t ]  with varEq x y
...                     | yes refl = Λ y α
...                     | no  x≢y  with t freeFor x In α
(Λ y α [ x / t ]) | no x≢y | yes x₁ = Λ y (α [ x / t ])
(Λ y α [ x / t ]) | no x≢y | no x₁ = {!   !}
  where
    ω : Variable
    ω = first
V y α   [ x / t ]  with varEq x y
...                     | yes refl = V y α
...                     | no  x≢y  = V y (α [ x / t ])


--subFreeFor : ∀{α x t β} → (α [ x / t ]) ≡ β → t FreeFor x In α
--
--
--subFreeFor (ident (atom r ts) x) = atom r ts
--subFreeFor (ident (α ⇒ β) x) = subFreeFor (ident α x) ⇒ subFreeFor (ident β x)
--subFreeFor (ident (α ∧ β) x) = subFreeFor (ident α x) ∧ subFreeFor (ident β x)
--subFreeFor (ident (α ∨ β) x) = subFreeFor (ident α x) ∨ subFreeFor (ident β x)
--subFreeFor (ident (Λ y α) x) with varEq y x
--...                          | yes refl = Λ↓ α
--...                          | no  y≢x  = Λ (varterm y≢x) (subFreeFor (ident α x))
--subFreeFor (ident (V y α) x) with varEq y x
--...                          | yes refl = V↓ α
--...                          | no  y≢x  = V (varterm y≢x) (subFreeFor (ident α x))
--subFreeFor (notfree x) = notfree x
--subFreeFor (atom r subts) = atom r _
--subFreeFor (subα ⇒ subβ) = subFreeFor subα ⇒ subFreeFor subβ
--subFreeFor (subα ∧ subβ) = subFreeFor subα ∧ subFreeFor subβ
--subFreeFor (subα ∨ subβ) = subFreeFor subα ∨ subFreeFor subβ
--subFreeFor (Λ↓ x α) = Λ↓ α
--subFreeFor (V↓ x α) = V↓ α
--subFreeFor (Λ x≢y y∉t sub) = Λ y∉t (subFreeFor sub)
--subFreeFor (V x≢y y∉t sub) = V y∉t (subFreeFor sub)
--
--
--subNotFree : ∀{α x t β} → x NotInTerm t → α [ x / t ]≡ β → x NotFreeIn β
--subNotFree (varterm x≢x) (ident α x)   = ⊥-elim (x≢x refl)
--subNotFree x∉t           (notfree x∉α) = x∉α
--subNotFree x∉t (atom r subts)  = atom (φ x∉t subts)
--  where
--    φ : ∀{n x t} {us vs : Vec Term n}
--        → x NotInTerm t → [ us ][ x / t ]≡ vs → x NotInTerms vs
--    φ x∉t []                     = []
--    φ x∉t (varterm≡     ∷ subus) = x∉t                  ∷ φ x∉t subus
--    φ x∉t (varterm≢ neq ∷ subus) = varterm neq          ∷ φ x∉t subus
--    φ x∉t (functerm sub ∷ subus) = functerm (φ x∉t sub) ∷ φ x∉t subus
--subNotFree x∉t (subα ⇒ subβ)   = subNotFree x∉t subα ⇒ subNotFree x∉t subβ
--subNotFree x∉t (subα ∧ subβ)   = subNotFree x∉t subα ∧ subNotFree x∉t subβ
--subNotFree x∉t (subα ∨ subβ)   = subNotFree x∉t subα ∨ subNotFree x∉t subβ
--subNotFree x∉t (Λ↓ y α)        = Λ↓ y α
--subNotFree x∉t (Λ x≢y y∉t sub) = Λ _ (subNotFree x∉t sub)
--subNotFree x∉t (V↓ y α)        = V↓ y α
--subNotFree x∉t (V x≢y y∉t sub) = V _ (subNotFree x∉t sub)
--
--
--subInverse : ∀{ω α x β} → ω NotFreeIn α
--                          → α [ x / varterm ω ]≡ β → β [ ω / varterm x ]≡ α
--subInverse _           (ident α x)    = ident α x
--subInverse ω∉α         (notfree x∉α)  = notfree ω∉α
--subInverse (atom x∉ts) (atom r subts) = atom r (φ x∉ts subts)
--  where
--    φ : ∀{n x ω} {us vs : Vec Term n}
--        → ω NotInTerms us → [ us ][ x / varterm ω ]≡ vs
--        → [ vs ][ ω / varterm x ]≡ us
--    φ ω∉us                   []                     = []
--    φ (_             ∷ ω∉us) (varterm≡     ∷ subus) = varterm≡
--                                                      ∷ φ ω∉us subus
--    φ (varterm ω≢y   ∷ ω∉us) (varterm≢ x≢ω ∷ subus) = varterm≢ ω≢y
--                                                      ∷ φ ω∉us subus
--    φ (functerm ω∉ts ∷ ω∉us) (functerm sub ∷ subus) = functerm (φ ω∉ts sub)
--                                                      ∷ φ ω∉us subus
--subInverse (ω∉α ⇒ ω∉β) (sα ⇒ sβ) = subInverse ω∉α sα ⇒ subInverse ω∉β sβ
--subInverse (ω∉α ∧ ω∉β) (sα ∧ sβ) = subInverse ω∉α sα ∧ subInverse ω∉β sβ
--subInverse (ω∉α ∨ ω∉β) (sα ∨ sβ) = subInverse ω∉α sα ∨ subInverse ω∉β sβ
--subInverse ω∉α (Λ↓ x α) = notfree ω∉α
--subInverse ω∉α (V↓ x α) = notfree ω∉α
--subInverse (Λ↓ x α) (Λ _ (varterm x≢x) _) = ⊥-elim (x≢x refl)
--subInverse (V↓ x α) (V _ (varterm x≢x) _) = ⊥-elim (x≢x refl)
--subInverse {ω} (Λ y ω∉α) (Λ _ y∉ω           _) with varEq ω y
--subInverse {ω} (Λ y ω∉α) (Λ _ (varterm y≢y) _) | yes refl = ⊥-elim (y≢y refl)
--subInverse {ω} (Λ y ω∉α) (Λ x≢y y∉ω sub)       | no  ω≢y
--    = Λ ω≢y (varterm λ { refl → x≢y refl }) (subInverse ω∉α sub)
--subInverse {ω} (V y ω∉α) (V _ y∉ω           _) with varEq ω y
--subInverse {ω} (V y ω∉α) (V _ (varterm y≢y) _) | yes refl = ⊥-elim (y≢y refl)
--subInverse {ω} (V y ω∉α) (V x≢y y∉ω sub)       | no  ω≢y
--    = V ω≢y (varterm λ { refl → x≢y refl }) (subInverse ω∉α sub)
--
--
