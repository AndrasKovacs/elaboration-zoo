{-# OPTIONS --type-in-type #-}

open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)
open import Relation.Binary.PropositionalEquality
open import Function

test : Set
test = Set where

  -- (Agda 2.6.1.3)

  -- works
  --------------------------------------------------------------------------------

  -- eliminating projections
  -- m : Set × Set
  -- m = _
  -- p₁ = (m .₁ ≡ Set) ∋ refl
  -- p₂ = (m .₂ ≡ Set) ∋ refl

  -- currying
  -- m : Set × Set → Set
  -- m = _
  -- p = λ (A : Set)(B : Set) → m (A , B) ≡ A ∋ refl

  -- nested currying
  -- m : Set × (Set × Set) → Set
  -- m = _
  -- p = λ (A : Set)(B : Set)(C : Set) → m (A , (B , C)) ≡ A ∋ refl

  -- projected variable under pairing
  -- m : Set × Set → Set
  -- m = _
  -- p = λ (A : Set)(B : Set × Set) → m (A , B .₁) ≡ B .₁ ∋ refl

  -- non-linearity
  -- m : Set → Set → Set → Set
  -- m = _
  -- p = λ (A : Set)(B : Set) → m A B B ≡ A ∋ refl
    -- m A B B =? A
    -- m = λ A _ _. A

    -- m : (a : A)(a' : A) → B a → B a' → C
    -- m a a (b : B a)(b' : B a)

  -- eta-reduction
  -- m : (Set → Set × Set) → Set
  -- m = _
  -- p = λ (f : Set → Set × Set) → m (λ x → f x .₁ , f x .₂) ≡ f Set .₁ ∋ refl
  --   =   p = λ (f : Set → Set × Set) → m f ≡ f Set .₁ ∋ refl

  -- doesn't work
  ------------------------------------------------------------

  -- non-linearity under pairing
  -- m : Set × Set × Set → Set
  -- m = _
  -- p = λ (A : Set)(B : Set) → m (A , B , B) ≡ A ∋ refl

  -- flipping
  -- m : (Set → Set → Set) → Set
  -- m = _
  -- p = λ (f : Set → Set → Set) → m (λ A B → f B A) ≡ f Set (Set → Set) ∋ refl

  -- projection under λ   (no full Skolemization)
  -- m : (Set → Set) → Set
  -- m = _
  -- p = λ (f : Set → Set × Set) → m (λ A → f A .₁) ≡ f Set .₁ ∋ refl

  -- flipping + projection
  -- m : (Set → Set × Set) → Set
  -- m = _
  -- p = λ (f : Set → Set × Set) → m (λ x → f x .₂ , f x .₁) ≡ f Set .₁ ∋ refl
