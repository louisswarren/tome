We give an example of proving scheme derivability.

\AgdaHide{
\begin{code}

open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)
open import Agda.Builtin.Sigma
open import Agda.Builtin.String

open import Decidable hiding (⊥ ; ¬_)
open import Deduction
open import Ensemble
open import Formula
open import List
open import Scheme
open import Texify
open import Vec

\end{code}
}

First, some syntactic sugar. The \inline{pattern} notation causes Adga to
recognise the notation in places where their values would be used in pattern
matching, and moreover will use the notation in proofs created by proof search.
Note that we are no longer using \inline{⊥} and \inline{¬} as defined
previously for decidable predicates in the metalanguage; here they are in the
language of formulae.
\begin{code}

pattern ⊥rel = rel zero zero
pattern ⊥ = atom ⊥rel []

pattern ¬ α = α ⇒ ⊥
pattern ¬¬ α = ¬ (¬ α)

\end{code}
We fix some variables, for defining schemes.
\begin{code}

pattern xvar   = var zero
pattern yvar   = var (suc zero)

x y : Term
x = varterm xvar
y = varterm yvar

pattern ∀x Φ = Λ xvar Φ
pattern ∃x Φ = V xvar Φ
pattern ¬∀x Φ = ¬(∀x Φ)
pattern ¬∃x Φ = ¬(∃x Φ)
pattern ∀x¬ Φ = ∀x (¬ Φ)
pattern ∃x¬ Φ = ∃x (¬ Φ)

\end{code}
Define a nullary and a unary predicate, which will be used to instantiate the
scheme proofs for output as proof trees in \LaTeX.
\begin{code}

pattern Arel = rel 1 0
pattern A    = atom Arel []

pattern Prel = rel 5 1
pattern P t  = atom Prel (t ∷ [])

\end{code}
We define schemes DNE (double negation elimination), EFQ (ex falso quodlibet),
DP (the drinker paradox), and HE (the dual of the drinker paradox). The latter
two schemes will be described and examined in more detail in the next chapter.
\begin{code}

dne efq dp he : Formula → Formula
dne Φ  = ¬¬ Φ ⇒ Φ
efq Φ  = ⊥ ⇒ Φ
dp  Φx = ∃x(Φx ⇒ ∀x Φx)
he  Φx = ∃x(∃x Φx ⇒ Φx)

DNE EFQ DP HE : Scheme
DNE = unaryscheme dne
EFQ = unaryscheme efq
DP  = unaryscheme dp
HE  = unaryscheme he

\end{code}

The natural deduction system used to define \inline{_⊢_} is for minimal logic.
This can be extended to classical logic with the classical $\bot$ rule.
\begin{code}

⊥c-rule : Set₁
⊥c-rule = ∀{Γ} → ∀ α
         →      Γ ⊢ ⊥
           --------------- ⊥c
         →  Γ - (¬ α) ⊢ α

\end{code}
Similarly, the intuitionistic $\bot$ rule
\begin{code}

⊥i-rule : Set₁
⊥i-rule = ∀{Γ} → ∀ α
         →      Γ ⊢ ⊥
               ------- ⊥i
         →      Γ ⊢ α

\end{code}
gives an extension to intuitionistic logic.

The classical bottom rule holds if and only if DNE is derivable.
\begin{code}

dne→⊥c-rule : ⊢₁ dne → ⊥c-rule
dne→⊥c-rule ⊢dne α Γ⊢⊥ = close
                          (assembled-context (arrowintro (¬ α) Γ⊢⊥))
                          (λ x₁ z₁ z₂ → z₂ (λ z₃ → z₁ (λ z₄ → z₄) (λ z₄ → z₄ z₃)))
                          (arrowelim
                           (cite "DNE" (⊢dne α))
                           (arrowintro (¬ α)
                            Γ⊢⊥))

⊥c-rule→dne : ⊥c-rule → ⊢₁ dne
⊥c-rule→dne ⊢⊥c-rule α = close
                          from∅
                          (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₃ z₅))))
                          (arrowintro (¬¬ α)
                           (⊢⊥c-rule α
                            (arrowelim
                             (assume (¬¬ α))
                             (assume (¬ α)))))

\end{code}

The the intuitionistic bottom rule holds if and only if EFQ is derivable.
\begin{code}

efq→⊥i-rule : ⊢₁ efq → ⊥i-rule
efq→⊥i-rule ⊢efq α Γ⊢⊥ = close
                          (assembled-context Γ⊢⊥)
                          (λ x₁ z₁ → z₁ (λ z₂ → z₂))
                          (arrowelim
                           (cite "EFQ" (⊢efq α))
                           Γ⊢⊥)

⊥i-rule→dne : ⊥i-rule → ⊢₁ efq
⊥i-rule→dne ⊢⊥i-rule α = close
                          from∅
                          (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃)))
                          (arrowintro ⊥
                           (⊢⊥i-rule α
                            (assume ⊥)))

\end{code}

We now show that DP holds clasically, by showing that it is weaker than
DNE, so that DP is derivable if DNE is derivable.
\begin{code}

dne→dp : ⊢₁ dne → ⊢₁ dp
dne→dp ⊢dne α = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄
                  (λ z₆ → z₆ (λ _ z₇ → z₇ (λ z₈ → z₈) (λ z₈ → z₈ (λ z₉ z₁₀ → z₁₀
                   z₄ (λ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ (λ z₁₄ → z₁₄) (λ z₁₄ → z₁₄
                    (λ _ z₁₅ → z₁₅ z₉ z₁₂))))))))))))
                 (arrowelim
                  (cite "DNE" (⊢dne (dp α)))
                  (arrowintro (¬ (dp α))
                   (arrowelim
                    (assume (¬ (dp α)))
                    (existintro x xvar (ident (α ⇒ ∀x α) xvar)
                     (arrowintro α
                      (univintro xvar
                       (all∅ all∪ (all- (all⟨ V∣ xvar (α ⇒ ∀x α) ⇒ atom [] ⟩
                        all∪ (all- (all∅ all∪ (all- (all⟨- ¬∀x α ∷ (α ∷
                         [ refl ]) ⟩ all∪ all⟨- ¬∀x α ∷ [ refl ] ⟩)))))))
                       (arrowelim
                        (cite "DNE" (⊢dne α))
                        (arrowintro (¬ α)
                         (arrowelim
                          (assume (¬ (dp α)))
                          (existintro x xvar (ident (α ⇒ ∀x α) xvar)
                          (arrowintro α
                           (arrowelim
                            (cite "DNE" (⊢dne (∀x α)))
                            (arrowintro (¬∀x α)
                             (arrowelim
                              (assume (¬ α))
                              (assume α)))))))))))))))
DNE⊃DP : DNE ∷ [] ⊃ DP
DNE⊃DP ⊢lhs (α ∷ []) = dne→dp (descheme₁ (⊢lhs DNE [ refl ])) α

dp-prooftree = texreduce DNE⊃DP (P x ∷ [])

\end{code}

This is a general derivation of an arbitrary instance of DP using instances of
DNE. The final line gets the deduction tree for the instance $\text{DP}({Px})$,
which is shown below, with instances of DP abbreviated, and split into two, due
to page constraints.

\begin{prooftree}
  \AxiomC{$\left[\lnot{\text{DP}({Px})}\right]$}
    \AxiomC{}
    \RightLabel{DNE}
    \UnaryInfC{$\lnot{\lnot{\forall_{x}P{x}}} \rightarrow \forall_{x}P{x}$}
      \AxiomC{$\left[\lnot{P{x}}\right]$}
        \AxiomC{$\left[P{x}\right]$}
      \RightLabel{$\rightarrow^-$}
      \BinaryInfC{$\bot$}
      \RightLabel{$\rightarrow^+$}
      \UnaryInfC{$\lnot{\lnot{\forall_{x}P{x}}}$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\forall_{x}P{x}$}
    \RightLabel{$\rightarrow^+$}
    \UnaryInfC{$P{x} \rightarrow \forall_{x}P{x}$}
    \RightLabel{$\exists^+$}
    \UnaryInfC{$\text{DP}({Px})$}
  \RightLabel{$\rightarrow^-$}
  \BinaryInfC{$\bot$}
  \UnaryInfC{$\vdots$}
\end{prooftree}
\begin{prooftree}
\AxiomC{}
\RightLabel{DNE}
\UnaryInfC{$\lnot{\lnot{\text{DP}({Px})}} \rightarrow \text{DP}({Px})$}
    \AxiomC{$\left[\lnot{\text{DP}({Px})}\right]$}
      \AxiomC{}
      \RightLabel{DNE}
      \UnaryInfC{$\lnot{\lnot{P{x}}} \rightarrow P{x}$}
        \AxiomC{$\vdots$}
        \UnaryInfC{$\bot$}
        \RightLabel{$\rightarrow^+$}
        \UnaryInfC{$\lnot{\lnot{P{x}}}$}
      \RightLabel{$\rightarrow^-$}
      \BinaryInfC{$P{x}$}
      \RightLabel{$\forall^+$}
      \UnaryInfC{$\forall_{x}P{x}$}
      \RightLabel{$\rightarrow^+$}
      \UnaryInfC{$P{x} \rightarrow \forall_{x}P{x}$}
      \RightLabel{$\exists^+$}
      \UnaryInfC{$\text{DP}({Px})$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\bot$}
    \RightLabel{$\rightarrow^+$}
    \UnaryInfC{$\lnot{\lnot{\text{DP}({Px})}}$}
  \RightLabel{$\rightarrow^-$}
  \BinaryInfC{$\exists_{x}\left(P{x} \rightarrow \forall_{x}P{x}\right)$}
\end{prooftree}

Similarly, the dual of the drinker paradox also holds in classical logic.
\begin{code}

dne→he : ⊢₁ dne → ⊢₁ he
dne→he ⊢dne α = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄
                  (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ z₉ → z₉) (λ z₉ → z₉ (λ _ z₁₀ → z₁₀
                   z₇ (λ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ z₄ (λ z₁₄ → z₁₄ (λ _ →
                    z₁₂))))))))))))
                 (arrowelim
                  (cite "DNE" (⊢dne (he α)))
                  (arrowintro (¬ (he α))
                   (arrowelim
                    (assume (¬ (he α)))
                    (existintro x xvar (ident (∃x α ⇒ α) xvar)
                     (arrowintro (∃x α)
                      (arrowelim
                       (cite "DNE" (⊢dne α))
                       (arrowintro (¬ α)
                        (existelim
                         (all⟨ atom [] ⟩ all∪ (all- (all⟨ V∣ xvar (∃x α ⇒ α)
                          ⇒ atom [] ⟩ all∪ (all- all⟨- ∃x α ∷ [ refl ] ⟩))))
                         (assume (∃x α))
                         (arrowelim
                          (assume (¬ (he α)))
                          (existintro x xvar (ident (∃x α ⇒ α) xvar)
                           (arrowintro (∃x α)
                            (assume α))))))))))))
DNE⊃HE : DNE ∷ [] ⊃ HE
DNE⊃HE ⊢lhs (α ∷ []) = dne→he (descheme₁ (⊢lhs DNE [ refl ])) α

he-prooftree = texreduce DNE⊃HE (P x ∷ [])

\end{code}

\begin{prooftree}
  \AxiomC{$\left[\exists_{x}P{x}\right]$}
    \AxiomC{$\left[\lnot{\text{HE}(Px)}\right]$}
      \AxiomC{$\left[P{x}\right]$}
      \RightLabel{$\rightarrow^+$}
      \UnaryInfC{$\exists_{x}P{x} \rightarrow P{x}$}
      \RightLabel{$\exists^+$}
      \UnaryInfC{$\text{HE}(Px)$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\bot$}
  \RightLabel{$\exists^-$}
  \BinaryInfC{$\bot$}
  \UnaryInfC{$\vdots$}
\end{prooftree}

\begin{prooftree}
\AxiomC{}
\RightLabel{DNE}
\UnaryInfC{$\lnot{\lnot{\text{HE}(Px)}} \rightarrow \text{HE}(Px)$}
  \AxiomC{$\left[\lnot{\text{HE}(Px)}\right]$}
    \AxiomC{}
    \RightLabel{DNE}
    \UnaryInfC{$\lnot{\lnot{P{x}}} \rightarrow P{x}$}
      \AxiomC{$\vdots$}
      \UnaryInfC{$\bot$}
      \RightLabel{$\rightarrow^+$}
      \UnaryInfC{$\lnot{\lnot{P{x}}}$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$P{x}$}
    \RightLabel{$\rightarrow^+$}
    \UnaryInfC{$\exists_{x}P{x} \rightarrow P{x}$}
    \RightLabel{$\exists^+$}
    \UnaryInfC{$\text{HE}(Px)$}
  \RightLabel{$\rightarrow^-$}
  \BinaryInfC{$\bot$}
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\lnot{\lnot{\text{HE}(Px)}}$}
\RightLabel{$\rightarrow^-$}
\BinaryInfC{$\text{HE}(Px)$}
\end{prooftree}

As a final example, consider these two formulations of the law of excluded
middle (we will forgo defining them as schemes for this example).
\begin{code}

lem ∃lem : Formula → Formula
lem  Φ = Φ ∨ (¬ Φ)
∃lem Φ = ∃x (lem Φ)

\end{code}
While the variable $x$ is fixed, it is expected that these are equivalent with
respect to derivability. That is, in an extension of minimal logic where one is
derivable, the other should also be derivable. The former leads to the latter
trivially. The other direction is more complicated, since $\Phi$ could have $x$
free. We use fresh variables, as defined in the formula section above. Find a
variable $\omega$ which is fresh in $\exists_x Px$, so that it is fresh in $Px$
and is not equal to $x$. Now $\exists_x (\text{LEM}({P\omega}) \vdash
\text{LEM}({Px})$.

\begin{prooftree}
\AxiomC{}
\RightLabel{$\exists$LEM}
\UnaryInfC{$\exists_{x}\left(P{\omega} \lor \lnot{P{\omega}}\right)$}
  \AxiomC{$\left[P{\omega} \lor \lnot{P{\omega}}\right]$}
\RightLabel{$\exists^-$}
\BinaryInfC{$P{\omega} \lor \lnot{P{\omega}}$}
\RightLabel{$\forall^+$}
\UnaryInfC{$\forall_{\omega}\left(P{\omega} \lor \lnot{P{\omega}}\right)$}
\RightLabel{$\forall^-$}
\UnaryInfC{$P{x} \lor \lnot{P{x}}$}
\end{prooftree}

First, define the above proof tree, deferring to lemata for proofs that
$\text{LEM}(P\omega)[\omega/x] = \text{LEM}(Px)$ and $x$ is not free in
$P\omega$.
\begin{code}

∃lem→lem : ⊢₁ ∃lem → ⊢₁ lem
∃lem→lem ⊢∃lem α = close
                    from∅
                    (λ x₁ z z₁ → z₁ (z (λ z₂ → z₂) (λ z₂ → z₂ (λ z₃ → z₃))))
                    (univelim x lemαω[ω/x]≡lemα
                     (univintro ωvar (all∅ all∪ (all- all⟨- [ refl ] ⟩))
                      (existelim (all⟨ x∉αω ∨ (x∉αω ⇒ atom []) ⟩
                                  all∪ (all- all⟨- [ refl ] ⟩))
                       (cite "$\\exists$LEM" (⊢∃lem αω))
                       (assume (lem αω)))))
  where
\end{code}
Compute the fresh variable, and use its construction to get that it is fresh in
$Px$ and not equal to $x$.
\begin{code}
    ω,ωFresh,x≢ω : Σ Variable (λ ω → Σ (ω FreshIn α) (λ _ → xvar ≢ ω))
    ω,ωFresh,x≢ω with fresh (∃x α)
    ω,ωFresh,x≢ω | ω , V x≢ω ωfrα = ω , ωfrα , x≢ω
\end{code}
We therefore have a variable $\omega$ which is not free in $Px$, which is free
for $x$ in $Px$, and which is different from $x$.
\begin{code}
    ωvar          : Variable
    ω∉α           : ωvar NotFreeIn α
    ωFreeForxInα  : (varterm ωvar) FreeFor xvar In α
    x≢ω           : xvar ≢ ωvar
    ωvar          = fst ω,ωFresh,x≢ω
    ω∉α           = freshNotFree (fst (snd ω,ωFresh,x≢ω))
    ωFreeForxInα  = freshFreeFor (fst (snd ω,ωFresh,x≢ω)) xvar
    x≢ω           = snd (snd ω,ωFresh,x≢ω)
\end{code}
Now, compute $P\omega = Px[\omega/x]$.
\begin{code}
    αω        : Formula
    α[x/ω]≡αω : α [ xvar / _ ]≡ αω
    αω        = fst (α [ xvar / ωFreeForxInα ])
    α[x/ω]≡αω = snd (α [ xvar / ωFreeForxInα ])
\end{code}
By the construction of $\omega$, the substitution is reversable, so
$\text{LEM}(P\omega)[\omega/x] = \text{LEM}(Px)$.
\begin{code}
    lemαω[ω/x]≡lemα : (lem αω) [ ωvar / _ ]≡ (lem α)
    lemαω[ω/x]≡lemα = subInverse
                       (ω∉α ∨ (ω∉α ⇒ atom []))
                       (α[x/ω]≡αω ∨ (α[x/ω]≡αω ⇒ notfree (atom [])))
\end{code}
Finally, $x$ will not be free after it has been substituted out of $Px$.
\begin{code}
    x∉αω : xvar NotFreeIn αω
    x∉αω = subNotFree (varterm x≢ω) α[x/ω]≡αω
    x∉lemαω : xvar NotFreeIn (lem αω)
    x∉lemαω = x∉αω ∨ (x∉αω ⇒ atom [])


∃LEM⊃LEM : (unaryscheme ∃lem) ∷ [] ⊃ (unaryscheme lem)
∃LEM⊃LEM ⊢lhs (α ∷ []) = ∃lem→lem (descheme₁ (⊢lhs (unaryscheme ∃lem) [ refl ])) α

r = texreduce ∃LEM⊃LEM (P x ∷ [])

glpo : Formula → Formula
glpo Φx = ∀x (¬ Φx) ∨ ∃x Φx

glpo→∃lem : ⊢₁ glpo → ⊢₁ ∃lem
glpo→∃lem ⊢glpo α = close
                     from∅
                     (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ → z₄ (λ z₅ → z₅)) (λ z₄ → z₄ (λ z₅ z₆ → z₆ z₅ (λ z₇ → z₇ (λ z₈ → z₈)))))))
                     (disjelim
                       (cite "GLPO" (⊢glpo α))
                       (existintro (varterm xvar) xvar (ident (α ∨ ¬ α) xvar)
                       (disjintro₂ α
                         (univelim x (ident (¬ α) xvar)
                         (assume (∀x¬ α)))))
                       (existelim (all⟨ V∣ xvar (α ∨ ¬ α) ⟩ all∪ (all- all⟨- [ refl ] ⟩))
                       (assume (∃x α))
                       (existintro x xvar (ident (α ∨ ¬ α) xvar)
                         (disjintro₁ (¬ α)
                         (assume α)))))

\end{code}
