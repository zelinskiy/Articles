
%<*name>
\begin{code}
\end{code}
%</name>

\begin{code}
module MLTT where
open import Agda.Primitive


id : ∀ {ℓ} {A : Set ℓ} → A → A
id = λ x → x





\end{code}

%<*logic>
\begin{code}
data ⊥ : Set where

record ⊤ : Set where
  constructor ⊤-cons

record _∨_ (A : Set) (B : Set) : Set where
  constructor _+_
  field
    in₁ : A
    in₂ : B

\end{code}
%</logic>

%<*sigma>
\begin{code}
record Σ {ℓ₁ ℓ₂} (A : Set ℓ₁) (P : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where  
  constructor Σ_,_
  field
    pr₁ : A       
    pr₂ : P pr₁
    
open Σ public

_×_ : (A B : Set) → Set 
A × B = Σ A (λ _ → B)
\end{code}
%</sigma>

%<*pi>
\begin{code}
Π : (A : Set) (B : A → Set) → Set
Π A B = (a : A) → B a

_⇒_ : (A B : Set) → Set
A ⇒ B = Π A (λ _ → B)
\end{code}
%</pi>

%<*id>
\begin{code}
data _≡_ {ℓ} {A : Set ℓ} (a : A) : A → Set ℓ where
  refl :  a ≡ a

sym : ∀ {ℓ} {A : Set ℓ} {a b : A} →
  a ≡ b → b ≡ a
sym refl = refl

trans :  ∀ {ℓ} {A : Set ℓ} {a b c : A} →
  a ≡ b → b ≡ c → a ≡ c
trans refl refl  = refl

cong :  ∀ {ℓ} {A : Set ℓ} {a b : A} {B : Set} {f : A → B} →
  a ≡ b → (f a) ≡ (f b)
cong refl = refl
\end{code}
%</id>

%<*ac>
\begin{code}
data R {A B : Set} (a : A) (b : B) : Set where

ac : {A B : Set} → Π A (λ a → Σ B (λ b → R a b)) →
  Σ (A → B) (λ f → (Π A (λ a → R a (f a))))
ac g = Σ (λ a → pr₁ (g a)) , (λ a → pr₂ (g a))
\end{code}
%</ac>

\begin{code}


ΠΣ : {A : Set} {B : A → Set} → Π A B → (a : A) → Σ A B
ΠΣ f x = Σ x , f x

infix 4 _≡_ 

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

{-
In Martin-Lof's papers appeared as:
data Id (A : Set) : A → A → Set where
  refl : {a : A} → Id A a a
-}


_○_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : {x : A} → B x → Set ℓ₃} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ○ g = λ x → f (g x)

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)


\end{code}
