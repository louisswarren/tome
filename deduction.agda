open import common
open import formula

module deduction where

_∖_ : List Formula → Formula → List Formula
[] ∖ _ = []
(x ∷ xs) ∖ a = if {! x =formula= a  !} then {!   !} else {!   !}

infixl 200 ∖

data Proof : List Formula → Formula →  Set
data Deduction : List Formula → Formula → Set

data Deduction where
  Cite        : ∀{α}
                → Proof [] α
                → Deduction [] α

  Assume      : (α : Formula)
                → Deduction [ α ] α

  ArrowIntro  : ∀{Γ β}
                → Deduction Γ β
                → (α : Formula)
                → Deduction (Γ ∖ α) (α ⇒ β)

  ArrowElim   : ∀{Γ₁ Γ₂ α β}
                → Deduction Γ₁ (α ⇒ β)
                → Deduction Γ₂ α
                → Deduction (Γ₁ ++ Γ₂) β

  ConjIntro   : ∀{Γ₁ Γ₂ α β}
                → Deduction Γ₁ α
                → Deduction Γ₂ β
                → Deduction (Γ₁ ++ Γ₂) (α ∧ β)

  ConjElim    : ∀{Γ₁ Γ₂ α β γ}
                → Deduction Γ₁ (α ∧ β)
                → Deduction Γ₂ γ
                → Deduction (Γ₁ ++ ((Γ₂ ∖ α) ∖ β)) γ

  DisjIntro₁  : ∀{Γ α}
                → Deduction Γ α
                → (β : Formula)
                → Deduction Γ (α ∨ β)

  DisjIntro₂  : ∀{Γ β}
                → Deduction Γ β
                → (α : Formula)
                → Deduction Γ (α ∨ β)

  DisjElim    : ∀{Γ₁ Γ₂ Γ₃ α β γ}
                → Deduction Γ₁ (α ∨ β)
                → Deduction Γ₂ γ
                → Deduction Γ₃ γ
                → Deduction (Γ₁ ++ (Γ₂ ∖ α) ++ (Γ₃ ∖ β)) γ

  UnivIntro   : ∀{Γ α}
                → (x : Variable)
                → Deduction Γ α
                → {_ : x NotFreeIn Γ}
                → Deduction Γ (universal x α)

  UnivElim    : ∀{Γ α x}
                → (t : Term)
                → Deduction Γ (universal x α)
                → Deduction Γ (α [ variableterm x / t ])

  ExistIntro  : ∀{Γ α}
                → (t : Term)
                → (x : Variable)
                → Deduction Γ α
                → Deduction Γ (existential x α [ t / variableterm x ])

  ExistElim   : ∀{Γ₁ Γ₂ α β x}
                → (a : Variable)
                → Deduction Γ₁ (existential x α)
                → Deduction Γ₂ β
                → {_ : a NotFreeIn [ β ]}
                → {_ : a NotFreeIn (Γ₂ ∖ (α [ variableterm x / variableterm a ]))}
                → Deduction (Γ₁ ++ (Γ₂ ∖ (α [ variableterm x / variableterm a ]))) β

  ClassAbsurd : ∀{Γ}
                → (α : Formula)
                → Deduction Γ ⊥
                → Deduction (Γ ∖ (¬ α)) α

  IntAbsurd   : ∀{Γ}
                → (α : Formula)
                → Deduction Γ ⊥
                → Deduction Γ α


conclusion : ∀{α Γ} → Deduction Γ α → Formula
conclusion {α} _ = α


assumptions : ∀{Γ α} → Deduction Γ α → List Formula
assumptions {Γ} _ = Γ


isMinimal : ∀{Γ α} → Deduction Γ α → Bool
isIntuitionistic : ∀{Γ α} → Deduction Γ α → Bool


data Proof where
  minimalproof        : ∀{Γ α}
                        → String
                        → (T : Deduction Γ α)
                        → {_ : isTrue (isMinimal T)}
                        → Proof Γ α

  intuitionisticproof : ∀{Γ α}
                        → String
                        → (T : Deduction Γ α)
                        → {_ : isTrue (isIntuitionistic T)}
                        → Proof Γ α

  classicalproof      : ∀{Γ α}
                        → String
                        → (T : Deduction Γ α)
                        → Proof Γ α


isMinimal (Cite (minimalproof        _ T)) = isMinimal T
isMinimal (Cite (intuitionisticproof _ T)) = isMinimal T
isMinimal (Cite (classicalproof      _ T)) = isMinimal T
isMinimal (Assume                 _) = true
isMinimal (ArrowIntro    T        _) = isMinimal T
isMinimal (ArrowElim     T₁ T₂     ) = isMinimal T₁ and isMinimal T₂
isMinimal (ConjIntro     T₁ T₂     ) = isMinimal T₁ and isMinimal T₂
isMinimal (ConjElim      T₁ T₂     ) = isMinimal T₁ and isMinimal T₂
isMinimal (DisjIntro₁    T        _) = isMinimal T
isMinimal (DisjIntro₂    T        _) = isMinimal T
isMinimal (DisjElim      T₁ T₂ T₃  ) = isMinimal T₁
                                         and isMinimal T₂ and isMinimal T₃
isMinimal (UnivIntro   _ T         ) = isMinimal T
isMinimal (UnivElim    _ T         ) = isMinimal T
isMinimal (ExistIntro _  _ T         ) = isMinimal T
isMinimal (ExistElim   _ T₁ T₂     ) = isMinimal T₁ and isMinimal T₂
isMinimal (ClassAbsurd _ T         ) = false
isMinimal (IntAbsurd   _ T         ) = false


isIntuitionistic (Cite (minimalproof        _ T)) = isIntuitionistic T
isIntuitionistic (Cite (intuitionisticproof _ T)) = isIntuitionistic T
isIntuitionistic (Cite (classicalproof      _ T)) = isIntuitionistic T
isIntuitionistic (Assume                 _) = true
isIntuitionistic (ArrowIntro    T        _) = isIntuitionistic T
isIntuitionistic (ArrowElim     T₁ T₂     ) = isIntuitionistic T₁
                                                and isIntuitionistic T₂
isIntuitionistic (ConjIntro     T₁ T₂     ) = isIntuitionistic T₁
                                                and isIntuitionistic T₂
isIntuitionistic (ConjElim      T₁ T₂     ) = isIntuitionistic T₁
                                                and isIntuitionistic T₂
isIntuitionistic (DisjIntro₁    T        _) = isIntuitionistic T
isIntuitionistic (DisjIntro₂    T        _) = isIntuitionistic T
isIntuitionistic (DisjElim      T₁ T₂ T₃  ) = isIntuitionistic T₁
                                                and isIntuitionistic T₂
                                                and isIntuitionistic T₃
isIntuitionistic (UnivIntro   _ T         ) = isIntuitionistic T
isIntuitionistic (UnivElim    _ T         ) = isIntuitionistic T
isIntuitionistic (ExistIntro _  _ T         ) = isIntuitionistic T
isIntuitionistic (ExistElim   _ T₁ T₂     ) = isIntuitionistic T₁
                                                and isIntuitionistic T₂
isIntuitionistic (ClassAbsurd _ T         ) = false
isIntuitionistic (IntAbsurd   _ T         ) = true
