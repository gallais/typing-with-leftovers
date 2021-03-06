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
  𝟘 𝟙  : Type
  _⊗_  : (σ τ : Type) → Type
  _─o_ : (σ τ : Type) → Type
  _&_  : (σ τ : Type) → Type
  _⊕_  : (σ τ : Type) → Type

data RType : Set where
  Base      : ℕ → RType
  Unit Zero : RType
  Tensor Lolli With Plus : (σ τ : RType) → RType

{-# FOREIGN GHC import Type.Parser #-}
{-# COMPILE GHC RType
    = data Type.Parser.Type
    (Type.Parser.Base
    | Type.Parser.Unit
    | Type.Parser.Zero
    | Type.Parser.Tensor
    | Type.Parser.Lolli
    | Type.Parser.With
    | Type.Parser.Plus)
#-}

embed^RType : RType → Type
embed^RType (Base x) = κ x
embed^RType Unit = 𝟙
embed^RType Zero = 𝟘
embed^RType (Tensor x x₁) = embed^RType x ⊗ embed^RType x₁
embed^RType (Lolli x x₁) = embed^RType x ─o embed^RType x₁
embed^RType (With x x₁) = embed^RType x & embed^RType x₁
embed^RType (Plus x x₁) = embed^RType x ⊕ embed^RType x₁

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
eq 𝟙          𝟙          = yes refl
eq 𝟘          𝟘          = yes refl
eq (σ₁ ⊗ τ₁)  (σ₂ ⊗ τ₂)  = eq⊗  <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (σ₁ ─o τ₁) (σ₂ ─o τ₂) = eq─o <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (σ₁ & τ₁)  (σ₂ & τ₂)  = eq&  <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (σ₁ ⊕ τ₁)  (σ₂ ⊕ τ₂)  = eq⊕  <$> eq σ₁ σ₂ <*> eq τ₁ τ₂
eq (κ _)      𝟙          = no (λ ())
eq (κ _)      𝟘          = no (λ ())
eq (κ _)      (_ ⊗ _)    = no (λ ())
eq (κ _)      (_ ─o _)   = no (λ ())
eq (κ _)      (_ & _)    = no (λ ())
eq (κ _)      (_ ⊕ _)    = no (λ ())
eq (_ ⊗ _)    (κ _)      = no (λ ())
eq (_ ⊗ _)    𝟙          = no (λ ())
eq (_ ⊗ _)    𝟘          = no (λ ())
eq (_ ⊗ _)    (_ ─o _)   = no (λ ())
eq (_ ⊗ _)    (_ & _)    = no (λ ())
eq (_ ⊗ _)    (_ ⊕ _)    = no (λ ())
eq (_ ─o _)   (κ _)      = no (λ ())
eq (_ ─o _)   𝟙          = no (λ ())
eq (_ ─o _)   𝟘          = no (λ ())
eq (_ ─o _)   (_ ⊗ _)    = no (λ ())
eq (_ ─o _)   (_ & _)    = no (λ ())
eq (_ ─o _)   (_ ⊕ _)    = no (λ ())
eq (_ ⊕ _)    (κ _)      = no (λ ())
eq (_ ⊕ _)    𝟙          = no (λ ())
eq (_ ⊕ _)    𝟘          = no (λ ())
eq (_ ⊕ _)    (_ ─o _)   = no (λ ())
eq (_ ⊕ _)    (_ & _)    = no (λ ())
eq (_ ⊕ _)    (_ ⊗ _)    = no (λ ())
eq (_ & _)    (κ _)      = no (λ ())
eq (_ & _)    𝟙          = no (λ ())
eq (_ & _)    𝟘          = no (λ ())
eq (_ & _)    (_ ⊗ _)    = no (λ ())
eq (_ & _)    (_ ─o _)   = no (λ ())
eq (_ & _)    (_ ⊕ _)    = no (λ ())
eq 𝟙          (κ _)      = no (λ ())
eq 𝟙          𝟘          = no (λ ())
eq 𝟙          (_ ⊗ _)    = no (λ ())
eq 𝟙          (_ ─o _)   = no (λ ())
eq 𝟙          (_ & _)    = no (λ ())
eq 𝟙          (_ ⊕ _)    = no (λ ())
eq 𝟘          (κ _)      = no (λ ())
eq 𝟘          𝟙          = no (λ ())
eq 𝟘          (_ ⊗ _)    = no (λ ())
eq 𝟘          (_ ─o _)   = no (λ ())
eq 𝟘          (_ & _)    = no (λ ())
eq 𝟘          (_ ⊕ _)    = no (λ ())

≟-diag : (n : ℕ) → (n ≟ n) ≡ yes refl
≟-diag zero = refl
≟-diag (suc n) rewrite ≟-diag n = refl

eq-diag : (σ : Type) → eq σ σ ≡ yes refl
eq-diag (κ n)    rewrite ≟-diag n = refl
eq-diag 𝟙 = refl
eq-diag 𝟘 = refl
eq-diag (σ ⊗ τ)  rewrite eq-diag σ | eq-diag τ = refl
eq-diag (σ ─o τ) rewrite eq-diag σ | eq-diag τ = refl
eq-diag (σ & τ)  rewrite eq-diag σ | eq-diag τ = refl
eq-diag (σ ⊕ τ)  rewrite eq-diag σ | eq-diag τ = refl
