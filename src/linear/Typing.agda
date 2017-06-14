module linear.Typing where

open import Data.Bool
open import Data.Nat as ℕ
open import Data.Fin
open import Data.Product
open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import linear.Type
open import linear.Scope as Sc
  hiding (Mergey ; copys ; Weakening ; weakFin ; Substituting ; substFin ; Env ; Freshey ; withFreshVars)
open import linear.Context as C hiding (Mergey ; _⋈_ ; copys ; _++_ ; ++copys-elim)
open import linear.Language as L
  hiding (patternSize ; weakInfer ; weakCheck ; substInfer ; substCheck ; Env
         ; fresheyInfer)
open import linear.Usage

infix 3 _⊢_∋_⊠_ _⊢_∈_⊠_ _∋_↝_
mutual
  
  data _⊢_∋_⊠_ {n : ℕ} {γ : Context n} (Γ : Usages γ) : (A : Type!) (t : Check n) (Δ : Usages γ) → Set where

    `lam_ : {σ τ : Type!} {b : Check (suc n)} {Δ : Usages γ} →
    
             fresh σ ∷ Γ ⊢ τ ∋ b ⊠ stale σ ∷ Δ →
           -------------------------
            Γ ⊢ σ ⊸ τ ∋ `lam b ⊠ Δ

    `let_∷=_`in_ : {σ τ : Type!} {o : ℕ} {p : Pattern o} {δ : Context o} {t : Infer n}
                  {Δ θ : Usages γ} {u : Check (o ℕ.+ n)} →

              σ ∋ p ↝ δ → Γ ⊢ t ∈ σ ⊠ Δ → f⌜ δ ⌝ ++ Δ ⊢ τ ∋ u ⊠ s⌜ δ ⌝ ++ θ →
            -----------------------------------------------------------------
                 Γ ⊢ τ ∋ `let p ∷= t `in u ⊠ θ

    `unit : --------------------
             Γ ⊢ 𝟙 ∋ `unit ⊠ Γ

    `prd⊗ : {σ τ : Type!} {a b : Check n} {Δ θ : Usages γ} →

             Γ ⊢ σ ∋ a ⊠ Δ → Δ ⊢ τ ∋ b ⊠ θ →
           ---------------------------------
             Γ ⊢ σ ⊗ τ ∋ `prd a b ⊠ θ


    `prd& : {σ τ : Type!} {a b : Check n} {Δ : Usages γ} →

             Γ ⊢ σ ∋ a ⊠ Δ → Γ ⊢ τ ∋ b ⊠ Δ →
           ---------------------------------
             Γ ⊢ σ & τ ∋ `prd a b ⊠ Δ


    `inl_ : {σ τ : Type!} {t : Check n} {Δ : Usages γ} →

                  Γ ⊢ σ ∋ t ⊠ Δ →
           ---------------------------------
               Γ ⊢ σ ⊕ τ ∋ `inl t ⊠ Δ

    `inr_ : {σ τ : Type!} {t : Check n} {Δ : Usages γ} →

                  Γ ⊢ τ ∋ t ⊠ Δ →
           ---------------------------------
               Γ ⊢ σ ⊕ τ ∋ `inr t ⊠ Δ


    `box_ : {σ : Type} {t : Check n} {Δ : Usages γ} →

             □ Γ ⊢ σ !^ false ∋ t ⊠ □ Δ →
           ------------------------------
               Γ ⊢ σ !^ true  ∋ t ⊠ Δ


    `neu_ : {σ : Type!} {t : Infer n} {Δ : Usages γ} →

             Γ ⊢ t ∈ σ ⊠ Δ →
           ---------------------
            Γ ⊢ σ ∋ `neu t ⊠ Δ
    
  data _⊢_∈_⊠_ {n : ℕ} {γ : Context n} (Γ : Usages γ) : (t : Infer n) (A : Type!) (Δ : Usages γ) → Set where

    `var_ : {σ : Type!} {Δ : Usages γ} {k : Fin n} →

             Γ ⊢var k ∈ σ ⊠ Δ →
          ----------------------
            Γ ⊢ `var k ∈ σ ⊠ Δ
            
    `app : {σ τ : Type!} {b : Bool} {Δ θ : Usages γ} {t : Infer n} {u : Check n} →

            Γ ⊢ t ∈ σ `⊸ τ !^ b ⊠ Δ → Δ ⊢ σ ∋ u ⊠ θ →
          --------------------------------------------
             Γ ⊢ `app t u ∈ τ ⊠ θ            

    `fst_ : {σ τ : Type!} {b : Bool} {Δ : Usages γ} {t : Infer n} →

            Γ ⊢ t ∈ σ `& τ !^ b ⊠ Δ →
          ----------------------------
            Γ ⊢ `fst t ∈ σ ⊠ Δ

    `snd_ : {σ τ : Type!} {Δ : Usages γ} {t : Infer n} →

            Γ ⊢ t ∈ σ & τ ⊠ Δ →
          -----------------------
            Γ ⊢ `snd t ∈ τ ⊠ Δ

    `case_return_of_%%_ : {σ τ : Type!} {Δ θ : Usages γ} {t : Infer n} {l r : Check (suc n)} →

            Γ ⊢ t ∈ σ ⊕ τ ⊠ Δ →
            (ν : Type!) →
            fresh σ ∷ Δ ⊢ ν ∋ l ⊠ stale σ ∷ θ →
            fresh τ ∷ Δ ⊢ ν ∋ r ⊠ stale τ ∷ θ →
          ---------------------------------------------
             Γ ⊢ `case t return ν of l %% r ∈ ν ⊠ θ            

    `exfalso : {Δ : Usages γ} {t : Infer n} →

            (σ : Type!) →
            Γ ⊢ t ∈ 𝟘 ⊠ Δ →
          ----------------------------
            Γ ⊢ `exfalso σ t ∈ σ ⊠ Δ

    `cut  : {σ : Type!} {Δ : Usages γ} {t : Check n} →

              Γ ⊢ σ ∋ t ⊠ Δ →
          -----------------------
           Γ ⊢ `cut t σ ∈ σ ⊠ Δ

  data _∋_↝_ : (A : Type!) {m : ℕ} (p : Pattern m) (Δ : Context m) → Set where
    `v   : {σ : Type!} → σ ∋ `v ↝ σ ∷ []
    `⟨⟩  : 𝟙 ∋ `⟨⟩ ↝ []
    _,,_ : {σ τ : Type!} {b : Bool} {m n : ℕ} {p : Pattern m} {q : Pattern n}
           {Δ₁ : Context m} {Δ₂ : Context n} →
           σ !! b ∋ p ↝ Δ₁ → τ !! b ∋ q ↝ Δ₂ → σ `⊗ τ !^ b ∋ p ,, q ↝ Δ₁ C.++ Δ₂



-- dirty hack
patternSize : {o : ℕ} {p : Pattern o} {σ : Type!} {γ : Context o} (p : σ ∋ p ↝ γ) → ℕ
patternSize {o} _ = o

patternContext : {o : ℕ} {p : Pattern o} {σ : Type!} {γ : Context o}
                 (p : σ ∋ p ↝ γ) → Context o
patternContext {γ = γ} _ = γ

checkOutput : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {σ : Type!} {t : Check n} →
              Γ ⊢ σ ∋ t ⊠ Δ → Usages γ
checkOutput {Δ = Δ} _ = Δ

inferOutput : {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {σ : Type!} {t : Infer n} →
              Γ ⊢ t ∈ σ ⊠ Δ → Usages γ
inferOutput {Δ = Δ} _ = Δ

TCheck : Typing Check
TCheck = λ Γ t A Δ → Γ ⊢ A ∋ t ⊠ Δ

TInfer : Typing Infer
TInfer = _⊢_∈_⊠_
