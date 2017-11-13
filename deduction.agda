open import common
open import formula

module deduction where


data Proof : List Formula → Formula →  Set
data Deduction : List Formula → Formula → Set



data DeductionList : List Formula → List Formula → Set where
  []   : DeductionList [] []
  _::_ : ∀{Γ α Γs αs}
         → Deduction Γ α
         → DeductionList Γs αs
         → DeductionList (Γ ++ Γs) (α :: αs)

lendl : ∀{Γs αs} → DeductionList Γs αs → ℕ
lendl []        = zero
lendl (x :: xs) = suc (lendl xs)

data Deduction where
  Collapse   : ∀{α Γs αs}
               → DeductionList Γs αs
               → Proof αs α
               → Deduction Γs α

  Assume     : (α : Formula)
               → Deduction [ α ] α

  ArrowIntro : ∀{Γ β}
               → Deduction Γ β
               → (α : Formula)
               → Deduction (Γ ∖ α) (α ⇒ β)

  ArrowElim  : ∀{Γ₁ Γ₂ α β}
               → Deduction Γ₁ (α ⇒ β)
               → Deduction Γ₂ α
               → Deduction (Γ₁ ++ Γ₂) β

  ConjIntro  : ∀{Γ₁ Γ₂ α β}
               → Deduction Γ₁ α
               → Deduction Γ₂ β
               → Deduction (Γ₁ ++ Γ₂) (α ∧ β)

  ConjElim   : ∀{Γ₁ Γ₂ α β γ}
               → Deduction Γ₁ (α ∧ β)
               → Deduction Γ₂ γ
               → Deduction (Γ₁ ++ (Γ₂ ∖ α ∖ β)) γ

  DisjIntro₁ : ∀{Γ α}
               → Deduction Γ α
               → (β : Formula)
               → Deduction Γ (α ∨ β)

  DisjIntro₂ : ∀{Γ β}
               → Deduction Γ β
               → (α : Formula)
               → Deduction Γ (α ∨ β)

  DisjElim   : ∀{Γ₁ Γ₂ Γ₃ α β γ}
               → Deduction Γ₁ (α ∨ β)
               → Deduction Γ₂ γ
               → Deduction Γ₃ γ
               → Deduction (Γ₁ ++ (Γ₂ ∖ α) ++ (Γ₃ ∖ β)) γ

  UnivIntro  : ∀{Γ α}
               → Deduction Γ α
               → (x : Term)
               → {_ : x notfreein Γ}
               → Deduction Γ (Α x α)

  UnivElim   : ∀{Γ α x}
               → (t : Term)
               → Deduction Γ (Α x α)
               → Deduction Γ (α [ x / t ])

  ExistIntro : ∀{Γ α}
               → Deduction Γ α
               → (x : Term)
               → Deduction Γ (Ε x α)

  ExistElim  : ∀{Γ₁ Γ₂ α β x}
               → (t : Term)
               → Deduction Γ₁ (Ε x α)
               → Deduction Γ₂ β
               → {_ : t notfreein [ β ]}
               → {_ : t notfreein (Γ₂ ∖ (α [ x / t ]))}
               → Deduction (Γ₁ ++ (Γ₂ ∖ (α [ x / t ]))) β

conclusion : ∀{α Γ} → Deduction Γ α → Formula
conclusion {α} _ = α

assumptions : ∀{Γ α} → Deduction Γ α → List Formula
assumptions {Γ} _ = Γ


data Proof where
  proof : ∀{Γ α} → String → Deduction Γ α → Proof Γ α
