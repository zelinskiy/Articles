

%<*main>
\begin{code}
module EqReason {a} {A : Set a} where
open import MLTT using (refl; _≡_; trans)

begin_ : ∀{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨_⟩_ : ∀ (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀ (x : A) → x ≡ x
_ ∎ = refl
\end{code}
%</main>

\begin{code}

infix  3 _∎
infixr 2 _≡⟨_⟩_ 
infix  1 begin_

\end{code}
