\begin{code}
module List where
open import MLTT using (_≡_; refl) renaming (_○_ to _∘_)
open import Nats
infixr 40 _::_
infixl 30 _++_


\end{code}

%<*listdef>
\begin{code}
data List {ℓ} (A : Set ℓ) : Set ℓ where
  [] : List A
  _::_ : (x : A) (xs : List A) → List A

_++_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

\end{code}
%</listdef> 


%<*funs>
\begin{code}
map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → List A → List B
map f [] = []
map f (x :: xs) = (f x) :: map f xs

length : ∀ {ℓ} {A : Set ℓ} → List A → ℕ
length [] = zero
length (x :: xs) = suc (length xs)

reverse :  ∀ {ℓ} {A : Set ℓ} → List A → List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ x :: []
\end{code}
%</funs>

%<*functor>
\begin{code}
map-∘ : ∀ {ℓ} {A B C : Set ℓ}(f : B → C)
  (g : A → B) (xs : List A) →
  map (f ∘ g) xs ≡ ((map f) ∘ (map g)) xs
map-∘ f g [] = refl
map-∘ f g (x :: xs) rewrite map-∘ f g xs = refl
\end{code}
%</functor>

\begin{code}
length-homo : ∀ {ℓ} {A : Set ℓ} → (xs : List A) → (ys : List A) →
  length (xs ++ ys) ≡ length xs + length ys
length-homo [] ys = refl
length-homo (x :: xs) ys rewrite length-homo xs ys = refl
\end{code}


%<*reverse>
\begin{code}
--length-homo : length (xs ++ ys) ≡ length xs + length ys
reverse-preserves-length : ∀ {ℓ} {A : Set ℓ} → (xs : List A)
  → length (reverse xs) ≡ length xs
reverse-preserves-length [] = refl
reverse-preserves-length (x :: xs) rewrite
  reverse-preserves-length xs |
  length-homo (reverse xs) (x :: []) |
  reverse-preserves-length xs |
  +comm (length xs) 1
  = refl
\end{code}
%</reverse>


\begin{code}

foldr : ∀ {ℓ} {A B : Set ℓ} → (A → B → B) → B → List A → B
foldr f i [] = i
foldr f i (x :: xs) = f x (foldr f i xs)
\end{code}
