
\begin{code}
module MonFunMon where
open import MLTT hiding (_∘_) renaming (_○_ to _∘_)
open import List
open import Nats
open import Agda.Primitive
open import EqReason

++-assoc : ∀ {ℓ} {A : Set ℓ} → (xs ys zs : List A) →
  xs ++ ys ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs rewrite ++-assoc xs ys zs = refl
\end{code}


%<*monoid>
\begin{code}
record Monoid {ℓ} (M : Set ℓ) : Set ℓ where
  field
    ε : M
    _·_ : M → M → M
    ·-assoc : (x y z : M) → ((x · y) · z) ≡ (x · (y · z))

mconcat : ∀ {ℓ} {M : Set ℓ} {{_ : Monoid M}} → List M → M
mconcat = foldr _·_ ε
  where open Monoid {{...}} 
\end{code}
%</monoid>


%<*listmonoid>
\begin{code}
instance
  listMonoid : ∀ {ℓ} {A : Set ℓ} → Monoid (List A)
  listMonoid = record {
    ε = [];
    _·_ = _++_ ;
    ·-assoc = ++-assoc }

t0 : List ℕ
t0 = mconcat ((1 :: 2 :: 3 :: []) :: (5 :: 6 :: 7 :: []) :: []) 

\end{code}
%</listmonoid>



%<*functor>
\begin{code}
record Functor {ℓ} (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
    law1 : ∀ {A} → (func : F A) → fmap id func ≡ id func
    law2 : ∀ {A B C} (g : B → C) (h : A → B) (f : F A) →
      fmap (g ∘ h) f ≡ ((fmap g) ∘ (fmap h)) f

fmap2 : {A B : Set } {F : Set → Set} {G : Set → Set}
  {{r1 : Functor G }} {{r2 : Functor F}} →
  (A → B) → G (F A) → G (F B)
fmap2 = fmap ∘ fmap where open Functor {{...}}
\end{code}
%</functor>

%<*listfunctor>
\begin{code}
l1 : ∀ {ℓ} {A : Set ℓ} → (xs : List A) → map id xs ≡ xs
l1 [] = refl
l1 (x :: xs) rewrite l1 xs = refl

instance
  functorList : ∀ {ℓ} → Functor (List {ℓ})
  functorList = record {
    fmap = map;
    law1 = l1;
    law2 = map-∘ }
\end{code}
%</listfunctor>



%<*monad>
\begin{code}
record Monad {ℓ₁ ℓ₂} (M : Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
  field
    return : ∀ {A} → A → M A
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B
    lidentity : ∀ {A B} → (a : A) (f : A → M B) →
      (return a) >>= f ≡ f a
    ridentity : ∀ {A} → (m : M A) → m >>= return ≡ m
    assoc : ∀ {A B C} → (m : M A) (f : A → M B) (g : B → M C) →
      (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
\end{code}
%</monad>

\begin{code}
data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  Nothing : Maybe A
  Just : A → Maybe A
\end{code}

%<*maybemonad>
\begin{code} 
instance
  MaybeMonad : ∀ {ℓ} → Monad (Maybe {ℓ})
  MaybeMonad = record {
   return = Just; 
   _>>=_ = λ { Nothing _ → Nothing; (Just x) f → f x};
   lidentity = λ x f → refl;
   ridentity = λ { Nothing → refl; (Just _) → refl};
   assoc =  λ { Nothing _ _ → refl; (Just _) _ _ → refl} }
\end{code}
%</maybemonad>
