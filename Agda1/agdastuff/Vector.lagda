\begin{code}
module Vector where
open import Nats
infixr 5 _∷_
\end{code}

%<*vecdef>
\begin{code}


data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

_++_ : ∀ {a m n} {A : Set a} →
  Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

\end{code}
%</vecdef> 
