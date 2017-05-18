
\begin{code}
module Bool where
open import Agda.Primitive using (_⊔_)
open import MLTT using (_≡_; refl)
\end{code}

%<*defbool>
\begin{code}
data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹
\end{code}
%</defbool>

%<*defops>
\begin{code}
infixl 5 _∧_

_∧_ : 𝔹 → 𝔹 → 𝔹
tt ∧ tt = tt
a  ∧ b  = ff

infixl 4 _∨_

_∨_ : 𝔹 → 𝔹 → 𝔹
tt ∨ b = tt
ff ∨ b = b
\end{code}
%</defops>

%<*idemp>
\begin{code}

∧-idemp : ∀ (x : 𝔹) → (x ∧ x) ≡ x
∧-idemp tt = refl
∧-idemp ff = refl

\end{code}
%</idemp>

%<*distrib>
\begin{code}

∧-distr-∨ : ∀ {x y z} → (x ∧ (y ∨ z)) ≡ ((x ∧ y) ∨ (x ∧ z))
∧-distr-∨ {tt} {tt} {z} = refl
∧-distr-∨ {tt} {ff} {z} = refl
∧-distr-∨ {ff} {tt} {z} = refl
∧-distr-∨ {ff} {ff} {z} = refl


\end{code}
%</distrib>

%<*absorp>
\begin{code}

∧-∨-absorp : ∀ {a b} → (a ∧ (a ∨ b)) ≡ tt → a ≡ tt
∧-∨-absorp {tt} p = refl
∧-∨-absorp {ff} ()

\end{code}
%</absorp>
