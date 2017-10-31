open import common
open import formula

module deduction where

data Deduction : List Formula → Formula → Set where
  Assume     : (p : Formula)
               → Deduction [ p ] p

  ArrowIntro : ∀{Γ q}
               → Deduction Γ q
               → (p : Formula)
               → Deduction (Γ ∖ p) (p ⇒ q)

  ArrowElim  : ∀{Γ₁ Γ₂ p q}
               → Deduction Γ₁ (p ⇒ q)
               → Deduction Γ₂ p
               → Deduction (Γ₁ ++ Γ₂) q

  ConjIntro  : ∀{Γ₁ Γ₂ p q}
               → Deduction Γ₁ p
               → Deduction Γ₂ q
               → Deduction (Γ₁ ++ Γ₂) (p ∧ q)

  ConjElim   : ∀{Γ₁ Γ₂ p q r}
               → Deduction Γ₁ (p ∧ q)
               → Deduction Γ₂ r
               → Deduction (Γ₁ ++ (Γ₂ ∖ p ∖ q)) r

  DisjIntro₁ : ∀{Γ p}
               → Deduction Γ p
               → (q : Formula)
               → Deduction Γ (p ∨ q)

  DisjIntro₂ : ∀{Γ q}
               → Deduction Γ q
               → (p : Formula)
               → Deduction Γ (p ∨ q)

  DisjElim   : ∀{Γ₁ Γ₂ Γ₃ p q r}
               → Deduction Γ₁ (p ∨ q)
               → Deduction Γ₂ r
               → Deduction Γ₃ r
               → Deduction (Γ₁ ++ (Γ₂ ∖ p) ++ (Γ₃ ∖ q)) r

  UniGIntro  : ∀{Γ p x}
               → x NotFreeIn Γ
               → Deduction Γ p
               → (x : Term)
               → Deduction Γ (Α x p)

  UniGElim   : ∀{Γ p x}
               → (y : Term)
               → Deduction Γ (Α x p)
               → Deduction Γ (p [ x / y ])

  ExiGIntro  : ∀{Γ p}
               → Deduction Γ p
               → (x : Term)
               → Deduction Γ (Ε x p)

  ExiGElim   : ∀{Γ₁ Γ₂ p q x}
               → (y : Term)
               → {_ : isTrue (not (y freein q))}
               → Deduction Γ₁ (Ε x p)
               → Deduction Γ₂ q
               → y NotFreeIn (Γ₂ ∖ (p [ x / y ]))
               → Deduction (Γ₁ ++ (Γ₂ ∖ (p [ x / y ]))) q

conclusion : ∀{p Γ} → Deduction Γ p → Formula
conclusion {p} _ = p

assumptions : ∀{Γ p} → Deduction Γ p → List Formula
assumptions {Γ} _ = Γ
