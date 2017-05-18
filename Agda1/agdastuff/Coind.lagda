


%<*imaginary>
\begin{code}
postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

infix 1000 ♯_

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

data Stream (A : Set) : Set where
  _::_ : A → ∞ (Stream A) → Stream A
\end{code}
%</imaginary>

\begin{code}
infixr 5 _::_
open import Nats
open import Vector renaming (_∷_ to _:V:_)
open import MLTT
\end{code}

\begin{code}

\end{code}

%<*rec>
\begin{code}
take : {A : Set} (n : ℕ) → Stream A → Vec A n
take zero    xs       = []
take (suc n) (x :: xs) = x :V: take n (♭ xs)

drop : {A : Set} → ℕ → Stream A → Stream A
drop zero xs = xs
drop (suc n) (x :: xs) = drop n (♭ xs)
\end{code}
%</rec>


%<*corec>
\begin{code}
iterate : {A : Set} → (A → A) → A → Stream A
iterate f x = x :: ♯ iterate (f ∘ f) x

map : {A B : Set} → (A → B) → Stream A → Stream B
map f (x :: xs) = f x :: ♯ map f (♭ xs)

zipWith : {A B C : Set} → (A → B → C) →
  Stream A → Stream B → Stream C
zipWith z (x :: xs) (y :: ys) =
  z x y :: ♯ zipWith z (♭ xs) (♭ ys)
\end{code}
%</corec>


%<*equiv>
\begin{code}

data _≈_ {A : Set} : Stream A → Stream A → Set where
  _::_ : (x : A) {xs ys : ∞ (Stream A)} → 
        ∞ (♭ xs ≈ ♭ ys) → x :: xs ≈ x :: ys

infix 4 _≈_

\end{code}
%</equiv>

%<*proofs>
\begin{code}
srefl : {A : Set} {xs : Stream A} →
  xs ≈ xs
srefl {A} {x :: xs} = x :: ♯ srefl

ssym : {A : Set} {xs ys : Stream A} →
  xs ≈ ys → ys ≈ xs
ssym (x :: xs) = x :: ♯ ssym (♭ xs)

strans : {A : Set} {xs ys zs : Stream A} →
  xs ≈ ys → ys ≈ zs → xs ≈ zs
strans (x :: xs) (.x :: ys) =
  x :: ♯ strans (♭ xs) (♭ ys)
\end{code}
%</proofs>
