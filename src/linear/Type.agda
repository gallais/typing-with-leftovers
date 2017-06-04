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
infixr 3 _⊸_

data   Type : Set
record Type! : Set

data Type where
  `κ    : ℕ → Type
  `𝟘 `𝟙 : Type
  _`⊗_  : (σ τ : Type!) → Type
  _`⊸_  : (σ τ : Type!) → Type
  _`&_  : (σ τ : Type!) → Type
  _`⊕_  : (σ τ : Type!) → Type

infix 6 _!^_
record Type! where
  inductive
  constructor _!^_
  field type  : Type
        bangs : ℕ

pattern 𝟘 = `𝟘 !^ 0
pattern 𝟙 = `𝟙 !^ 0
pattern κ n = `κ n !^ 0
pattern _⊗_ σ τ = σ `⊗ τ !^ 0
pattern _⊸_ σ τ = σ `⊸ τ !^ 0
pattern _&_ σ τ = σ `& τ !^ 0
pattern _⊕_ σ τ = σ `⊕ τ !^ 0

infixl 5 _!
_! : Type! → Type!
σ !^ n ! = σ !^ suc n

-- Equality of types is decidable
`κ-inj : {x y : ℕ} → `κ x ≡ `κ y → x ≡ y
`κ-inj refl = refl

eq`κ : {x y : ℕ} → RawIso (x ≡ y) (`κ x ≡ `κ y)
eq`κ = mkRawIso (cong `κ) `κ-inj

`⊗-inj : {σ₁ τ₁ σ₂ τ₂ : Type!} → σ₁ `⊗ τ₁ ≡ σ₂ `⊗ τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
`⊗-inj refl = refl , refl

eq`⊗ : {σ₁ τ₁ σ₂ τ₂ : Type!} →
       RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ `⊗ τ₁ ≡ σ₂ `⊗ τ₂)
eq`⊗ = mkRawIso (uncurry (cong₂ _`⊗_)) `⊗-inj

`⊕-inj : {σ₁ τ₁ σ₂ τ₂ : Type!} → σ₁ `⊕ τ₁ ≡ σ₂ `⊕ τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
`⊕-inj refl = refl , refl

eq`⊕ : {σ₁ τ₁ σ₂ τ₂ : Type!} →
       RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ `⊕ τ₁ ≡ σ₂ `⊕ τ₂)
eq`⊕ = mkRawIso (uncurry (cong₂ _`⊕_)) `⊕-inj

`⊸-inj : {σ₁ τ₁ σ₂ τ₂ : Type!} → σ₁ `⊸ τ₁ ≡ σ₂ `⊸ τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
`⊸-inj refl = refl , refl

`&-inj : {σ₁ τ₁ σ₂ τ₂ : Type!} → σ₁ `& τ₁ ≡ σ₂ `& τ₂ → σ₁ ≡ σ₂ × τ₁ ≡ τ₂
`&-inj refl = refl , refl

eq`& : {σ₁ τ₁ σ₂ τ₂ : Type!} →
       RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ `& τ₁ ≡ σ₂ `& τ₂)
eq`& = mkRawIso (uncurry (cong₂ _`&_)) `&-inj

eq`⊸ : {σ₁ τ₁ σ₂ τ₂ : Type!} →
        RawIso (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) (σ₁ `⊸ τ₁ ≡ σ₂ `⊸ τ₂)
eq`⊸ = mkRawIso (uncurry (cong₂ _`⊸_)) `⊸-inj

!^-inj : {σ₁ σ₂ : Type} {m n : ℕ} → σ₁ !^ m ≡ σ₂ !^ n → σ₁ ≡ σ₂ × m ≡ n
!^-inj refl = refl , refl

eq!^ : {σ₁ σ₂ : Type} {m n : ℕ} →
       RawIso (σ₁ ≡ σ₂ × m ≡ n) (σ₁ !^ m ≡ σ₂ !^ n)
eq!^ = mkRawIso (uncurry (cong₂ _!^_)) !^-inj


eq  : (σ τ : Type)  → Dec (σ ≡ τ)
eq! : (σ τ : Type!) → Dec (σ ≡ τ)

eq (`κ x)     (`κ y)     = eq`κ  <$> x ≟ y
eq `𝟙         `𝟙          = yes refl
eq `𝟘         `𝟘          = yes refl
eq (σ₁ `⊗ τ₁)  (σ₂ `⊗ τ₂)  = eq`⊗  <$> eq! σ₁ σ₂ <*> eq! τ₁ τ₂
eq (σ₁ `⊸ τ₁) (σ₂ `⊸ τ₂) = eq`⊸ <$> eq! σ₁ σ₂ <*> eq! τ₁ τ₂
eq (σ₁ `& τ₁)  (σ₂ `& τ₂)  = eq`&  <$> eq! σ₁ σ₂ <*> eq! τ₁ τ₂
eq (σ₁ `⊕ τ₁)  (σ₂ `⊕ τ₂)  = eq`⊕  <$> eq! σ₁ σ₂ <*> eq! τ₁ τ₂
eq (`κ _)      `𝟙          = no (λ ())
eq (`κ _)      `𝟘          = no (λ ())
eq (`κ _)      (_ `⊗ _)    = no (λ ())
eq (`κ _)      (_ `⊸ _)   = no (λ ())
eq (`κ _)      (_ `& _)    = no (λ ())
eq (`κ _)      (_ `⊕ _)    = no (λ ())
eq (_ `⊗ _)    (`κ _)      = no (λ ())
eq (_ `⊗ _)    `𝟙          = no (λ ())
eq (_ `⊗ _)    `𝟘          = no (λ ())
eq (_ `⊗ _)    (_ `⊸ _)   = no (λ ())
eq (_ `⊗ _)    (_ `& _)    = no (λ ())
eq (_ `⊗ _)    (_ `⊕ _)    = no (λ ())
eq (_ `⊸ _)   (`κ _)      = no (λ ())
eq (_ `⊸ _)   `𝟙          = no (λ ())
eq (_ `⊸ _)   `𝟘          = no (λ ())
eq (_ `⊸ _)   (_ `⊗ _)    = no (λ ())
eq (_ `⊸ _)   (_ `& _)    = no (λ ())
eq (_ `⊸ _)   (_ `⊕ _)    = no (λ ())
eq (_ `⊕ _)    (`κ _)      = no (λ ())
eq (_ `⊕ _)    `𝟙          = no (λ ())
eq (_ `⊕ _)    `𝟘          = no (λ ())
eq (_ `⊕ _)    (_ `⊸ _)   = no (λ ())
eq (_ `⊕ _)    (_ `& _)    = no (λ ())
eq (_ `⊕ _)    (_ `⊗ _)    = no (λ ())
eq (_ `& _)    (`κ _)      = no (λ ())
eq (_ `& _)    `𝟙          = no (λ ())
eq (_ `& _)    `𝟘          = no (λ ())
eq (_ `& _)    (_ `⊗ _)    = no (λ ())
eq (_ `& _)    (_ `⊸ _)   = no (λ ())
eq (_ `& _)    (_ `⊕ _)    = no (λ ())
eq `𝟙          (`κ _)      = no (λ ())
eq `𝟙          `𝟘          = no (λ ())
eq `𝟙          (_ `⊗ _)    = no (λ ())
eq `𝟙          (_ `⊸ _)   = no (λ ())
eq `𝟙          (_ `& _)    = no (λ ())
eq `𝟙          (_ `⊕ _)    = no (λ ())
eq `𝟘          (`κ _)      = no (λ ())
eq `𝟘          `𝟙          = no (λ ())
eq `𝟘          (_ `⊗ _)    = no (λ ())
eq `𝟘          (_ `⊸ _)   = no (λ ())
eq `𝟘          (_ `& _)    = no (λ ())
eq `𝟘          (_ `⊕ _)    = no (λ ())

eq! (σ !^ m) (τ !^ p) = eq!^ <$> eq σ τ <*> m ≟ p

≟-diag : (n : ℕ) → (n ≟ n) ≡ yes refl
≟-diag zero = refl
≟-diag (suc n) rewrite ≟-diag n = refl

eq-diag  : (σ : Type)  → eq σ σ ≡ yes refl
eq!-diag : (σ : Type!) → eq! σ σ ≡ yes refl

eq-diag (`κ n) rewrite ≟-diag n = refl
eq-diag `𝟙 = refl
eq-diag `𝟘 = refl
eq-diag (σ `⊗ τ)  rewrite eq!-diag σ | eq!-diag τ = refl
eq-diag (σ `⊸ τ) rewrite eq!-diag σ | eq!-diag τ = refl
eq-diag (σ `& τ)  rewrite eq!-diag σ | eq!-diag τ = refl
eq-diag (σ `⊕ τ)  rewrite eq!-diag σ | eq!-diag τ = refl

eq!-diag (σ !^ m) rewrite eq-diag σ | ≟-diag m = refl
