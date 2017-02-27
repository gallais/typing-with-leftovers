module linear.Examples where

open import Data.Nat
open import Data.Fin

open import linear.Type
open import linear.Context
open import linear.Usage hiding ([_])
open import linear.Language
open import linear.Typing
open import linear.Language.SmartConstructors

⊢swap⊗ : {σ τ : Type} → [] ⊢ (σ ⊗ τ) ─o (τ ⊗ σ) ∋ _ ⊠ []
⊢swap⊗ =
  `lam `let (`v ,, `v) ∷= [ 0 ] `in
       `prd⊗ (`neu [ 1 ]) (`neu [ 0 ])

⊗⊕-distr : (σ τ ν : Type) → [] ⊢ (σ ⊗ (τ ⊕ ν)) ─o (σ ⊗ τ) ⊕ (σ ⊗ ν) ∋ _ ⊠ []
⊗⊕-distr σ τ ν =
  `lam `let (`v ,, `v) ∷= [ 0 ] `in
       `neu `case `var (s z) return (σ ⊗ τ) ⊕ (σ ⊗ ν)
            of `inl (`prd⊗ [ 1 ] [ 0 ])
            %% `inr (`prd⊗ [ 1 ] [ 0 ])
