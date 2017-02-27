module linear.Language.SmartConstructors where

open import Data.Bool
open import Data.Nat as ℕ
open import Data.Fin
open import Data.Vec hiding ([_])
open import linear.Type
open import linear.Context
open import linear.Usage as U hiding ([_])
open import linear.Language as L
open import linear.Typing   as T
open import linear.Typecheck
open import linear.Typecheck.Problem
open import Relation.Nullary
open import linear.Relation.Nullary
open import Function

record VAR (T : ℕ → Set) (𝓣 : Typing T) : Set where
  field
    mkVarT  : ∀ {n} → Fin n → T n
    mkVar𝓣 : ∀ {n γ} {Γ : Usages γ} {σ} {k : Fin n} {Δ} →
              Γ ⊢ k ∈[ σ ]⊠ Δ →  𝓣 Γ (mkVarT k) σ Δ
open VAR {{...}} public

[_] : ∀ {n} k {pr : T (isYes (suc k ℕ.≤? n))} {γ : Context n} {Γ : Usages γ} →
      let k′ = fromℕ≤ (fromYes _ {pr}) in
      {pr′ : T (isYes (consume Γ k′))} →
      let (σ , Δ , _) = fromYes _ {pr′}
      in ∀ {T} {𝓣 : Typing T} {{V : VAR T 𝓣}} → 𝓣 Γ (mkVarT {{V}} k′) σ Δ
[ k ] {pr′ = pr′} {{V}} = mkVar𝓣 {{V}} $ CONSUME.proof $ fromYes _ {pr′}


instance

  VARFin : VAR Fin TFin
  VAR.mkVarT  VARFin = id
  VAR.mkVar𝓣 VARFin = id

  VARInfer : VAR Infer TInfer
  VAR.mkVarT  VARInfer = `var_
  VAR.mkVar𝓣 VARInfer = `var_

  VARCheck : VAR Check TCheck
  VAR.mkVarT  VARCheck k = `neu `var k
  VAR.mkVar𝓣 VARCheck K = `neu `var K
