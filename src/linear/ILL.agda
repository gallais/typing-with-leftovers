module linear.ILL where

open import Data.List hiding (_∷ʳ_)
open import linear.Type
open import linear.Usage.Erasure
open import Function
open import Algebra
import Relation.Binary.PropositionalEquality as PEq

-- This presentation of ILL is taken from:
-- http://llwiki.ens-lyon.fr/mediawiki/index.php/Intuitionistic_linear_logic
-- except for the `mix` constructor allowing the user to reorganise the
-- context (on the llwiki, the context is a multiset).

infix 1 _⊢_
data _⊢_ : List Type → Type → Set where
  ax  : {σ : Type} → (σ ∷ []) ⊢ σ
  cut : {γ δ : List Type} {σ τ : Type} → γ ⊢ σ → σ ∷ δ ⊢ τ → γ ++ δ ⊢ τ
  ⊗R  : {γ δ : List Type} {σ τ : Type} → γ ⊢ σ → δ ⊢ τ → γ ++ δ ⊢ σ ⊗ τ
  ⊗L  : {γ : List Type} {σ τ ν : Type} → τ ∷ σ ∷ γ ⊢ ν → σ ⊗ τ ∷ γ ⊢ ν
  ─oR : {γ : List Type} {σ τ : Type} → σ ∷ γ ⊢ τ → γ ⊢ σ ─o τ
  ─oL : {γ δ : List Type} {σ τ ν : Type} → γ ⊢ σ → τ ∷ δ ⊢ ν → (σ ─o τ) ∷ γ ++ δ ⊢ ν
  &R  : {γ : List Type} {σ τ : Type} → γ ⊢ σ → γ ⊢ τ → γ ⊢ σ & τ
  &₁L : {γ : List Type} {σ τ ν : Type} → σ ∷ γ ⊢ ν  → σ & τ ∷ γ ⊢ ν
  &₂L : {γ : List Type} {σ τ ν : Type} → τ ∷ γ ⊢ ν  → σ & τ ∷ γ ⊢ ν
  ⊕₁R : {γ : List Type} {σ τ : Type} → γ ⊢ σ → γ ⊢ σ ⊕ τ
  ⊕₂R : {γ : List Type} {σ τ : Type} → γ ⊢ τ → γ ⊢ σ ⊕ τ
  ⊕L  : {γ : List Type} {σ τ ν : Type} → σ ∷ γ ⊢ ν → τ ∷ γ ⊢ ν → σ ⊕ τ ∷ γ ⊢ ν
  mix : {γ δ θ : List Type} {σ : Type} → γ ++ δ ⊢ σ → γ ++ δ ≅ θ → θ ⊢ σ

-- We can derive the more traditional `swap` structural rule
-- from the `mix` constructor provided here.
swap : ∀ {γ δ σ τ ν} → γ ++ σ ∷ τ ∷ δ ⊢ ν → γ ++ τ ∷ σ ∷ δ ⊢ ν
swap {γ} {δ} {σ} {τ} p
  rewrite PEq.sym (Monoid.assoc (monoid Type) γ (σ ∷ []) (τ ∷ δ))
  = mix p $ γ ++ˡ τ ∷ʳ trivial
