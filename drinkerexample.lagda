We give an example of proving scheme derivability. We will also use a module
for outputting natural deduction trees as \LaTeX.

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
open import Vec

\end{code}
}

\begin{code}

open import Texify

\end{code}
The code for this is entirely computational, and so has been omitted.

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
Fix some variables.
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
The indices used for variables $x$ and $y$ and predicates $A$ and $P$ are
arbitrary, but correspond to those used internally by the texify module, so
they will be outputted with the same names.

Define the schemes DNE (double negation elimination), EFQ (ex falso quodlibet),
DP (the drinker paradox), and H$\epsilon$ (the dual of the drinker paradox).
The latter two schemes will be described and examined in more detail in the
next chapter.
\begin{code}

dne efq dp hε : Formula → Formula
dne Φ  = ¬¬ Φ ⇒ Φ
efq Φ  = ⊥ ⇒ Φ
dp  Φx = ∃x(Φx ⇒ ∀x Φx)
hε  Φx = ∃x(∃x Φx ⇒ Φx)

DNE EFQ DP Hε : Scheme
DNE = unaryscheme "DNE"          dne
EFQ = unaryscheme "EFQ"          efq
DP  = unaryscheme "DP"           dp
Hε  = unaryscheme "H$\\epsilon$" hε

\end{code}

The natural deduction system used to define \inline{_⊢_} is for minimal logic.
This can be extended to classical logic with the classical $\bot$ rule.
\todo{proof trees?}
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
                          (λ x₁ z₁ z₂
                           → z₂ (λ z₃ → z₁ (λ z₄ → z₄) (λ z₄ → z₄ z₃)))
                          (arrowelim
                           (⊢dne α)
                           (arrowintro (¬ α)
                            Γ⊢⊥))

⊥c-rule→dne : ⊥c-rule → ⊢₁ dne
⊥c-rule→dne ⊢⊥c-rule α = close
                          from∅
                          (λ x₁ z₁ z₂
                           → z₂ (z₁ (λ z₃ z₄ → z₄ (λ z₅ z₆ → z₆ z₃ z₅))))
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
                           (⊢efq α)
                           Γ⊢⊥)

⊥i-rule→dne : ⊥i-rule → ⊢₁ efq
⊥i-rule→dne ⊢⊥i-rule α = close
                          from∅
                          (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃)))
                          (arrowintro ⊥
                           (⊢⊥i-rule α
                            (assume ⊥)))

\end{code}

DP holds clasically. We show that if DNE is derivable then DP is derivable,
meaning that DP is weaker than DNE. For illustrative purposes, lines given by
Agda's proof search are marked with \inline{{- Auto -}} in the next proof.
\begin{code}

dne→dp : ⊢₁ dne → ⊢₁ dp
dne→dp ⊢dne α = close
  {- Auto -}     from∅
  {- Auto -}     (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄
  {- Auto -}      (λ z₆ → z₆ (λ _ z₇ → z₇ (λ z₈ → z₈) (λ z₈ → z₈ (λ z₉ z₁₀
  {- Auto -}       → z₁₀ z₄ (λ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ (λ z₁₄ → z₁₄)
  {- Auto -}        (λ z₁₄ → z₁₄ (λ _ z₁₅ → z₁₅ z₉ z₁₂))))))))))))
                 (arrowelim
                  (⊢dne (dp α))
                  (arrowintro (¬ (dp α))
                   (arrowelim
                    (assume (¬ (dp α)))
                    (existintro x xvar
  {- Auto -}         (ident (α ⇒ ∀x α) xvar)
                     (arrowintro α
                      (univintro xvar
  {- Auto -}           (all∅ all∪ (all- (all⟨ V∣ xvar (α ⇒ ∀x α) ⇒ atom [] ⟩
  {- Auto -}            all∪ (all- (all∅ all∪ (all- (all⟨- ¬∀x α ∷ (α ∷
  {- Auto -}             [ refl ]) ⟩ all∪ all⟨- ¬∀x α ∷ [ refl ] ⟩)))))))
                       (arrowelim
                        (⊢dne α)
                        (arrowintro (¬ α)
                         (arrowelim
                          (assume (¬ (dp α)))
                          (existintro x xvar
  {- Auto -}               (ident (α ⇒ ∀x α) xvar)
                           (arrowintro α
                            (arrowelim
                             (⊢dne (∀x α))
                             (arrowintro (¬∀x α)
                              (arrowelim
                               (assume (¬ α))
                               (assume α)))))))))))))))

\end{code}
This is a general derivation of an arbitrary instance of DP using instances of
DNE. We use this proof to construct the scheme relation `$\supset$', for
outputting as \LaTeX.
\begin{code}

DNE⊃DP : DNE ∷ [] ⊃ DP
DNE⊃DP ⊢lhs (α ∷ []) = dne→dp (descheme₁ (⊢lhs DNE [ refl ])) α
dp-prooftree = texreduce DP (P x ∷ []) DNE⊃DP

\end{code}
The final line gets the deduction tree for the instance $\text{DP}({Px})$,
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
\vspace{\baselineskip}

Similarly, the dual of the drinker paradox also holds in classical logic.
\begin{code}

dne→hε : ⊢₁ dne → ⊢₁ hε
dne→hε ⊢dne α = close
                 from∅
                 (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃ (λ z₄ z₅ → z₅ z₄
                  (λ z₆ → z₆ (λ z₇ z₈ → z₈ (λ z₉ → z₉) (λ z₉ → z₉ (λ _ z₁₀
                   → z₁₀ z₇ (λ z₁₁ → z₁₁ (λ z₁₂ z₁₃ → z₁₃ z₄ (λ z₁₄ → z₁₄
                    (λ _ → z₁₂))))))))))))
                 (arrowelim
                  (⊢dne (hε α))
                  (arrowintro (¬ (hε α))
                   (arrowelim
                    (assume (¬ (hε α)))
                    (existintro x xvar (ident (∃x α ⇒ α) xvar)
                     (arrowintro (∃x α)
                      (arrowelim
                       (⊢dne α)
                       (arrowintro (¬ α)
                        (existelim
                         (all⟨ atom [] ⟩ all∪ (all- (all⟨ V∣ xvar (∃x α ⇒ α)
                          ⇒ atom [] ⟩ all∪ (all- all⟨- ∃x α ∷ [ refl ] ⟩))))
                         (assume (∃x α))
                         (arrowelim
                          (assume (¬ (hε α)))
                          (existintro x xvar (ident (∃x α ⇒ α) xvar)
                           (arrowintro (∃x α)
                            (assume α))))))))))))

DNE⊃Hε : DNE ∷ [] ⊃ Hε
DNE⊃Hε ⊢lhs (α ∷ []) = dne→hε (descheme₁ (⊢lhs DNE [ refl ])) α
hε-prooftree = texreduce Hε (P x ∷ []) DNE⊃Hε

\end{code}

\begin{prooftree}
  \AxiomC{$\left[\exists_{x}P{x}\right]$}
    \AxiomC{$\left[\lnot{\text{H$\epsilon$}(Px)}\right]$}
      \AxiomC{$\left[P{x}\right]$}
      \RightLabel{$\rightarrow^+$}
      \UnaryInfC{$\exists_{x}P{x} \rightarrow P{x}$}
      \RightLabel{$\exists^+$}
      \UnaryInfC{$\text{H$\epsilon$}(Px)$}
    \RightLabel{$\rightarrow^-$}
    \BinaryInfC{$\bot$}
  \RightLabel{$\exists^-$}
  \BinaryInfC{$\bot$}
  \UnaryInfC{$\vdots$}
\end{prooftree}

\begin{prooftree}
\AxiomC{}
\RightLabel{DNE}
\UnaryInfC{$\lnot{\lnot{\text{H$\epsilon$}(Px)}} \rightarrow \text{H$\epsilon$}(Px)$}
  \AxiomC{$\left[\lnot{\text{H$\epsilon$}(Px)}\right]$}
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
    \UnaryInfC{$\text{H$\epsilon$}(Px)$}
  \RightLabel{$\rightarrow^-$}
  \BinaryInfC{$\bot$}
  \RightLabel{$\rightarrow^+$}
  \UnaryInfC{$\lnot{\lnot{\text{H$\epsilon$}(Px)}}$}
\RightLabel{$\rightarrow^-$}
\BinaryInfC{$\text{H$\epsilon$}(Px)$}
\end{prooftree}
\vspace{\baselineskip}

As a final example, consider the law of excluded middle, and a generalised form
of the limited principle of omniscience \todo{cite LPO}.
\begin{code}

lem glpo : Formula → Formula
lem  Φ = Φ ∨ (¬ Φ)
glpo Φ = ∀x (¬ Φ) ∨ ∃x Φ

LEM GLPO : Scheme
LEM  = unaryscheme "LEM"  lem
GLPO = unaryscheme "GLPO" glpo

\end{code}
Recall that equivalent formulae are equivalently derivable, so from GLPO we may
derive a form with any other quantifying variable. Therefore while the variable
$x$ is fixed, it can be expected that LEM and GPO are equivalent with respect
to derivability.  That is, in an extension of minimal logic where one is
derivable, the other should also be derivable. The former leads to the latter
trivially. The other direction is more complicated, since $\Phi$ could have $x$
free.

We show first that when deriving $\text{LEM}(\Phi)$, we may assume without
loss of generality that $x$ is not free in $\Phi$, by showing that if LEM is
derivable in this restricted case, then it is derivable in general.

Given any formula $\alpha$, there is a fresh variable $\omega$ which appears
nowhere in $\alpha$ and which differs from $x$. Then $\alpha[x/\omega]$ exists,
with $x$ not free, and $\alpha[x/\omega][\omega/x] = \alpha$. Now if LEM holds
for $\alpha[x/\omega]$ then it holds for $\alpha$, by the following proof tree.
\begin{prooftree}
  \AxiomC{}
  \UnaryInfC{$\alpha[x/\omega] \lor \lnot\alpha[x/\omega]$}
  \RightLabel{$\forall^+$}
  \UnaryInfC{$\forall_\omega \left(\alpha[x/\omega] \lor \lnot\alpha[x/\omega]\right)$}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\alpha \lor \lnot\alpha$}
\end{prooftree}
Hence we may derive LEM by deriving it only for formulae for which $x$ is not
free.  This is formalised in Agda as follows.
\begin{code}

wlog-lem : (∀ α → xvar NotFreeIn α → ⊢ (lem α)) → ⊢₁ lem
wlog-lem ⊢nflem α = close
                     from∅
                     (λ x₁ z₁ z₂ → z₂ z₁)
                     (univelim x lemαω[ω/x]≡lemα
                      (univintro ωvar all∅
                       (⊢nflem αω x∉αω)))
  where
\end{code}
Compute the fresh variable, and use its construction to get that it is fresh in
$\alpha$ and not equal to $x$.
\begin{code}
    ω,ωFresh,x≢ω : Σ Variable (λ ω → Σ (ω FreshIn α) (λ _ → xvar ≢ ω))
    ω,ωFresh,x≢ω with fresh (∀x α)
    ω,ωFresh,x≢ω | ω , Λ x≢ω ωFrα = ω , ωFrα , x≢ω
\end{code}
We therefore have a variable $\omega$ which is not free in $\alpha$, which is
free for $x$ in $\alpha$, and which is different from $x$.
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
Now, compute $\alpha_\omega = \alpha[\omega/x]$.
\begin{code}
    αω        : Formula
    α[x/ω]≡αω : α [ xvar / _ ]≡ αω
    αω        = fst (α [ xvar / ωFreeForxInα ])
    α[x/ω]≡αω = snd (α [ xvar / ωFreeForxInα ])
\end{code}
By the construction of $\omega$, the substitution is reversable, so
$\text{LEM}(\alpha_\omega)[\omega/x] = \text{LEM}(\alpha)$.
\begin{code}
    lemαω[ω/x]≡lemα : (lem αω) [ ωvar / _ ]≡ (lem α)
    lemαω[ω/x]≡lemα = subInverse
                       (ω∉α ∨ (ω∉α ⇒ atom []))
                       (α[x/ω]≡αω ∨ (α[x/ω]≡αω ⇒ notfree (atom [])))
\end{code}
Finally, $x$ will not be free after it has been substituted out of $\alpha$.
\begin{code}
    x∉αω : xvar NotFreeIn αω
    x∉αω = subNotFree (varterm x≢ω) α[x/ω]≡αω

\end{code}

We can now show that GLPO is stronger than LEM, without worrying about the
quantifier.
\todo{Don't call it rlem}
\begin{code}

glpo→xnf→lem : ⊢₁ glpo → ∀ α → xvar NotFreeIn α → ⊢ (lem α)
glpo→xnf→lem ⊢glpo α x∉α = close
                            from∅
                            (λ x₁ z₁ z₂ → z₂ (z₁ (λ z₃ → z₃) (λ z₃ → z₃
                             (λ z₄ → z₄ (λ z₅ → z₅)) (λ z₄ → z₄ (λ z₅ z₆ → z₆
                              z₅ (λ z₇ → z₇ (λ z₈ → z₈)))))))
                            (disjelim
                             (⊢glpo α)
                             (disjintro₂ α
                              (univelim x (ident (¬ α) xvar)
                               (assume (∀x¬ α))))
                             (disjintro₁ (¬ α)
                              (existelim (all⟨ x∉α ⟩ all∪ (all- all⟨ x∉α ⟩))
                               (assume (∃x α))
                               (assume α))))

\end{code}
Now, LEM can be obtained directly from GLPO. The proof tree for the restricted
form of LEM is inserted into the proof tree from \inline{wlog-lem}.
\begin{code}

glpo→lem : ⊢₁ glpo → ⊢₁ lem
glpo→lem ⊢glpo = wlog-lem (glpo→xnf→lem ⊢glpo)

GLPO⊃LEM : GLPO ∷ [] ⊃ LEM
GLPO⊃LEM ⊢lhs (α ∷ []) = glpo→lem (descheme₁ (⊢lhs GLPO [ refl ])) α

\end{code}
No computation of a fresh variable has occured yet, since the variable depends
on the instance of LEM we want to derive. Extracting the proof tree for
$\text{LEM}(Px)$, the \inline{fresh} function computes that $y$ is fresh, and
so the proof tree below is produced.
\begin{code}

glpo→lem-prooftree = texreduce LEM (P x ∷ []) GLPO⊃LEM

\end{code}

\begin{prooftree}
\AxiomC{}
\RightLabel{GLPO}
\UnaryInfC{$\forall_{x}\lnot{P{y}} \lor \exists_{x}P{y}$}
  \AxiomC{$\left[\forall_{x}\lnot{P{y}}\right]$}
  \RightLabel{$\forall^-$}
  \UnaryInfC{$\lnot{P{y}}$}
  \RightLabel{$\lor^+$}
  \UnaryInfC{$P{y} \lor \lnot{P{y}}$}
    \AxiomC{$\left[\exists_{x}P{y}\right]$}
      \AxiomC{$\left[P{y}\right]$}
    \RightLabel{$\exists^-$}
    \BinaryInfC{$P{y}$}
    \RightLabel{$\lor^+$}
    \UnaryInfC{$P{y} \lor \lnot{P{y}}$}
\RightLabel{$\lor^-$}
\TrinaryInfC{$P{y} \lor \lnot{P{y}}$}
\RightLabel{$\forall^+$}
\UnaryInfC{$\forall_{y}\left(P{y} \lor \lnot{P{y}}\right)$}
\RightLabel{$\forall^-$}
\UnaryInfC{$P{x} \lor \lnot{P{x}}$}
\end{prooftree}

