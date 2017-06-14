module linear.Type where

open import Function
open import Data.Nat as Nat
open import Data.Bool as Bool
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import linear.RawIso

infixr 9 _&_
infixr 8 _⊕_
infixr 7 _⊗_
infixr 6 _⊸_

data   Type : Set
record Type! : Set

data Type where
  `κ    : ℕ → Type
  `𝟘 `𝟙 : Type
  _`⊗_  : (σ τ : Type!) → Type
  _`⊸_  : (σ τ : Type!) → Type
  _`&_  : (σ τ : Type!) → Type
  _`⊕_  : (σ τ : Type!) → Type

infix 7 _!^_
record Type! where
  inductive
  constructor _!^_
  field type : Type
        bang : Bool

pattern 𝟘       = `𝟘 !^ false
pattern 𝟙       = `𝟙 !^ false
pattern κ n     = `κ n !^ false
pattern _⊗_ σ τ = σ `⊗ τ !^ false
pattern _⊸_ σ τ = σ `⊸ τ !^ false
pattern _&_ σ τ = σ `& τ !^ false
pattern _⊕_ σ τ = σ `⊕ τ !^ false

infixl 5 _! _!!_
_!!_ : Type! → Bool → Type!
σ !^ a !! b = σ !^ (b ∨ a)

_! : Type! → Type!
_! = _!! true

!^-inj : {σ τ : Type} {m n : Bool} → σ !^ m ≡ τ !^ n → σ ≡ τ × m ≡ n
!^-inj refl = refl , refl

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

eq!^ : {σ₁ σ₂ : Type} {m n : Bool} →
       RawIso (σ₁ ≡ σ₂ × m ≡ n) (σ₁ !^ m ≡ σ₂ !^ n)
eq!^ = mkRawIso (uncurry (cong₂ _!^_)) !^-inj


eq  : (σ τ : Type)  → Dec (σ ≡ τ)
eq! : (σ τ : Type!) → Dec (σ ≡ τ)

eq (`κ x)     (`κ y)     = eq`κ  <$> x Nat.≟ y
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

eq! (σ !^ m) (τ !^ p) = eq!^ <$> eq σ τ <*> m Bool.≟ p

Nat≟-diag : (n : ℕ) → (n Nat.≟ n) ≡ yes refl
Nat≟-diag zero = refl
Nat≟-diag (suc n) rewrite Nat≟-diag n = refl

Bool≟-diag : (n : Bool) → (n Bool.≟ n) ≡ yes refl
Bool≟-diag false = refl
Bool≟-diag true  = refl

eq-diag  : (σ : Type)  → eq σ σ ≡ yes refl
eq!-diag : (σ : Type!) → eq! σ σ ≡ yes refl

eq-diag (`κ n) rewrite Nat≟-diag n = refl
eq-diag `𝟙 = refl
eq-diag `𝟘 = refl
eq-diag (σ `⊗ τ)  rewrite eq!-diag σ | eq!-diag τ = refl
eq-diag (σ `⊸ τ) rewrite eq!-diag σ | eq!-diag τ = refl
eq-diag (σ `& τ)  rewrite eq!-diag σ | eq!-diag τ = refl
eq-diag (σ `⊕ τ)  rewrite eq!-diag σ | eq!-diag τ = refl

eq!-diag (σ !^ m) rewrite eq-diag σ | Bool≟-diag m = refl
