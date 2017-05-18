
\begin{code}

open import Agda.Primitive using (_⊔_)

\end{code}

%<*sigma>
\begin{code}

record Σ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor Σ_,_
  field
    pr₁ : A
    pr₂ : B pr₁

\end{code}
%<*/sigma>

