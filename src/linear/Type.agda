module linear.Type where

open import Function
open import Data.Nat
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import linear.RawIso

infixr 8 _&_
infixr 7 _⊕_
infixr 6 _⊗_
infixr 5 _─o_
data Type : Set where
  κ    : ℕ → Type
  _⊗_  : (σ τ : Type) → Type
  _─o_ : (σ τ : Type) → Type
  _&_  : (σ τ : Type) → Type
  _⊕_  : (σ τ : Type) → Type

{-# IMPORT Type.Parser #-}
{-# COMPILED_DATA
    Type Type.Parser.Type
    Type.Parser.Base
    Type.Parser.Tensor
    Type.Parser.Lolli
    Type.Parser.With
    Type.Parser.Plus
#-}

-- Equality of types is decidable
κ-inj : {x y : ℕ} → κ x ≡ κ y → x ≡ y
κ-inj refl = refl

eqκ : {x y : ℕ} → RawIso (x ≡ y) (κ x ≡ κ y)
eqκ = mkRawIso (cong κ) κ-inj

⊗-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → σ₁ ⊗ τ₁ ≡ σ₂ ⊗ τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
⊗-inj refl = refl , refl

eq⊗ : {σ₁ τ₁ σ₂ τ₂ : Type} →  RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ ⊗ τ₁ ≡ σ₂ ⊗ τ₂)
eq⊗ = mkRawIso (uncurry (cong₂ _⊗_)) ⊗-inj

⊕-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → σ₁ ⊕ τ₁ ≡ σ₂ ⊕ τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
⊕-inj refl = refl , refl

eq⊕ : {σ₁ τ₁ σ₂ τ₂ : Type} →  RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ ⊕ τ₁ ≡ σ₂ ⊕ τ₂)
eq⊕ = mkRawIso (uncurry (cong₂ _⊕_)) ⊕-inj

─o-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → σ₁ ─o τ₁ ≡ σ₂ ─o τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
─o-inj refl = refl , refl

&-inj : {σ₁ τ₁ σ₂ τ₂ : Type} → σ₁ & τ₁ ≡ σ₂ & τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
&-inj refl = refl , refl

eq& : {σ₁ τ₁ σ₂ τ₂ : Type} →  RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ & τ₁ ≡ σ₂ & τ₂)
eq& = mkRawIso (uncurry (cong₂ _&_)) &-inj

eq─o : {σ₁ τ₁ σ₂ τ₂ : Type} →  RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ ─o τ₁ ≡ σ₂ ─o τ₂)
eq─o = mkRawIso (uncurry (cong₂ _─o_)) ─o-inj

eq : (σ τ : Type) → Dec (σ ≡ τ)
eq (κ x)      (κ y)      = eqκ  <$> x ≟ y
eq (σ₁ ⊗ τ₁)  (σ₂ ⊗ τ₂)  = eq⊗  <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (σ₁ ─o τ₁) (σ₂ ─o τ₂) = eq─o <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (σ₁ & τ₁)  (σ₂ & τ₂)  = eq&  <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (σ₁ ⊕ τ₁)  (σ₂ ⊕ τ₂)  = eq⊕  <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (κ _)      (_ ⊗ _)    = no (λ ())
eq (κ _)      (_ ─o _)   = no (λ ())
eq (κ _)      (_ & _)    = no (λ ())
eq (κ _)      (_ ⊕ _)    = no (λ ())
eq (_ ⊗ _)    (κ _)      = no (λ ())
eq (_ ⊗ _)    (_ ─o _)   = no (λ ())
eq (_ ⊗ _)    (_ & _)    = no (λ ())
eq (_ ⊗ _)    (_ ⊕ _)    = no (λ ())
eq (_ ─o _)   (κ _)      = no (λ ())
eq (_ ─o _)   (_ ⊗ _)    = no (λ ())
eq (_ ─o _)   (_ & _)    = no (λ ())
eq (_ ─o _)   (_ ⊕ _)    = no (λ ())
eq (_ ⊕ _)    (κ _)      = no (λ ())
eq (_ ⊕ _)    (_ ─o _)   = no (λ ())
eq (_ ⊕ _)    (_ & _)    = no (λ ())
eq (_ ⊕ _)    (_ ⊗ _)    = no (λ ())
eq (_ & _)   (κ _)       = no (λ ())
eq (_ & _)   (_ ⊗ _)     = no (λ ())
eq (_ & _)   (_ ─o _)    = no (λ ())
eq (_ & _)   (_ ⊕ _)     = no (λ ())

≟-diag : (n : ℕ) → (n ≟ n) ≡ yes refl
≟-diag zero = refl
≟-diag (suc n) rewrite ≟-diag n = refl

eq-diag : (σ : Type) → eq σ σ ≡ yes refl
eq-diag (κ n)    rewrite ≟-diag n = refl
eq-diag (σ ⊗ τ)  rewrite eq-diag σ | eq-diag τ = refl
eq-diag (σ ─o τ) rewrite eq-diag σ | eq-diag τ = refl
eq-diag (σ & τ)  rewrite eq-diag σ | eq-diag τ = refl
eq-diag (σ ⊕ τ)  rewrite eq-diag σ | eq-diag τ = refl
