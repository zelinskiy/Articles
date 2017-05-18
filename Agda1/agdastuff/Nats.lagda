\begin{code}
module Nats where
open import MLTT using (_≡_; refl)

infixl 25 _+_
infixl 30 _*_
\end{code}

%<*natsdef>
\begin{code}
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc a * b = b + (a * b)

\end{code}
%</natsdef>


%<*leftplus>
\begin{code}
+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

\end{code}
%</leftplus>


%<*comm>
\begin{code}
+suc-lemma : ∀ (x y : ℕ) → x + (suc y) ≡ suc (x + y)
+suc-lemma zero y = refl
+suc-lemma (suc x) y rewrite +suc-lemma x y = refl

+comm : ∀ (x y : ℕ) → x + y ≡ y + x
+comm zero y rewrite +0 y = refl
+comm (suc x) y
  rewrite        -- suc x + y ≡ y + suc x    
  +comm x y |    -- suc (y + x) ≡ y + suc x  
  +suc-lemma y x -- suc (y + x) ≡ suc (y + x)
  = refl
\end{code}
%</comm>

\begin{code}
+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

*0 : ∀ (x : ℕ) → x * zero ≡ zero
*0 zero = refl
*0 (suc x) rewrite *0 x = refl

*suc-lemma : ∀ (x y : ℕ) → x * (suc y) ≡ x + x * y
*suc-lemma zero y = refl
*suc-lemma (suc x) y rewrite
    *suc-lemma x y
  | +assoc y x (x * y)
  | +assoc x y (x * y)
  | +comm y x
  = refl

*comm : ∀ (x y : ℕ) → x * y ≡ y * x
*comm zero y rewrite *0 y = refl
*comm (suc x) y rewrite
    *suc-lemma y x
  | *comm x y
  = refl
\end{code}


%<*distr>
\begin{code}
*ldistr+ : ∀ (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*ldistr+ x zero z
  rewrite              -- x * (zero + z) ≡ x * zero + x * z 
  *comm x (zero + z) | -- z * x ≡ x * 0 + z * x             
  *0 x                 -- z * x ≡ 0 + z * x                 
  = refl
*ldistr+ x (suc y) z
  rewrite                  -- x * (suc y + z) ≡ x * suc y + x * z     
  *suc-lemma x (y + z) |   -- x + x * (y + z) ≡ x * suc y + x * z     
  *suc-lemma x y |         -- x + x * (y + z) ≡ x + x * y + x * z     
  *ldistr+ x y z |         -- x + (x * y + x * z) ≡ x + x * y + x * z 
  +assoc x (x * y) (x * z) -- x + x * y + x * z ≡ x + x * y + x * z   
  = refl                    
\end{code}
%</distr>
