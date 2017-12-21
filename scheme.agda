open import common
open import deduction
open import formula

data _is_ {A : Set}(x : A) : A → Set where
  refl : x is x

-- WIll later need arbitrary arity schemes
Scheme = Formula → Formula

SchemeProof : (scm : Scheme) → ((p : Formula) → Deduction [] (scm p)) → Set
SchemeProof scm pf = (λ p → conclusion (pf p)) is scm


exs : Formula → Formula
exs p = ((p ⇒ p) ⇒ p) ⇒ p

postulate magic : ∀{p α}
                  → Deduction
                      (((p ⇒ p) ⇒ p :: ([] ++ [ p ] ∖ p)) ∖ ((p ⇒ p) ⇒ p)) α
                  → Deduction [] α

pf : (p : Formula) → Deduction [] (exs p)
pf p = magic {p} (ArrowIntro (ArrowElim (Assume ((p ⇒ p) ⇒ p))
                              (ArrowIntro (Assume p) p)) ((p ⇒ p) ⇒ p))


spf : SchemeProof exs pf
spf = refl
