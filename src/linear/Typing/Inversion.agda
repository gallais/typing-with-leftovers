module linear.Typing.Inversion where

open import Data.Nat
open import Data.Vec hiding (map ; [_] ; _++_)
open import Data.Product

open import linear.Type
open import linear.Context hiding (_++_)
open import linear.Language
open import linear.Usage
open import linear.Typing

-- inversion lemmas
app-inv :
  {n : ℕ} {γ : Context n} {t : Infer n} {u : Check n} {Γ Δ : Usages γ} {τ : Type} →
  Γ ⊢ `app t u ∈ τ ⊠ Δ → Σ[ θ ∈ Usages γ ] Σ[ σ ∈ Type ] Γ ⊢ t ∈ σ ─o τ ⊠ θ × θ ⊢ σ ∋ u ⊠ Δ
app-inv (`app t u) = , , t , u

skip-inv : 
  {n : ℕ} {γ : Context n} {t : Infer n} {u : Check n} {Γ Δ : Usages γ} {σ : Type} →
  Γ ⊢ `skip u t ∈ σ ⊠ Δ → Σ[ θ ∈ Usages γ ] Γ ⊢ 𝟙 ∋ u ⊠ θ × θ ⊢ t ∈ σ ⊠ Δ
skip-inv (`skip U T) = , U , T

fst-inv :
  {n : ℕ} {γ : Context n} {t : Infer n} {Γ Δ : Usages γ} {σ : Type} →
  Γ ⊢ `fst t ∈ σ ⊠ Δ → Σ[ τ ∈ Type ] Γ ⊢ t ∈ σ & τ ⊠ Δ
fst-inv (`fst t) = , t

snd-inv :
  {n : ℕ} {γ : Context n} {t : Infer n} {Γ Δ : Usages γ} {τ : Type} →
  Γ ⊢ `snd t ∈ τ ⊠ Δ → Σ[ σ ∈ Type ] Γ ⊢ t ∈ σ & τ ⊠ Δ
snd-inv (`snd t) = , t

case-inv : 
  {n : ℕ} {γ : Context n} {t : Infer n} {l r : Check (suc n)} {Γ Δ : Usages γ} {ν₁ ν₂ : Type} →
  Γ ⊢ `case t return ν₁ of l %% r ∈ ν₂ ⊠ Δ →
  Σ[ θ ∈ Usages γ ] Σ[ σ ∈ Type ] Σ[ τ ∈ Type ]
  Γ ⊢ t ∈ σ ⊕ τ ⊠ θ × [ σ ] ∷ θ ⊢ ν₁ ∋ l ⊠ ] σ [ ∷ Δ × [ τ ] ∷ θ ⊢ ν₁ ∋ r ⊠ ] τ [ ∷ Δ
case-inv (`case t return ν of l %% r) = , , , t , l , r

neu-inv :
  {n : ℕ} {γ : Context n} {t : Infer n} {Γ Δ : Usages γ} {σ : Type} →
  Γ ⊢ σ ∋ `neu t ⊠ Δ → Γ ⊢ t ∈ σ ⊠ Δ
neu-inv (`neu t) = t

lam-inv : 
  {n : ℕ} {γ : Context n} {t : Check (suc n)} {Γ Δ : Usages γ} {σ τ : Type} →
  Γ ⊢ σ ─o τ ∋ `lam t ⊠ Δ → [ σ ] ∷ Γ ⊢ τ ∋ t ⊠ ] σ [ ∷ Δ
lam-inv (`lam t) = t

let-inv : 
  {n o : ℕ} {γ : Context n} {p : Pattern o} {t : Infer n} {u : Check (o + n)}
  {Γ Δ : Usages γ} {τ : Type} → Γ ⊢ τ ∋ `let p ∷= t `in u ⊠ Δ →
  Σ[ θ ∈ Usages γ ] Σ[ σ ∈ Type ] Σ[ δ ∈ Context o ]
  Γ ⊢ t ∈ σ ⊠ θ × σ ∋ p ↝ δ × [[ δ ]] ++ θ ⊢ τ ∋ u ⊠ ]] δ [[ ++ Δ
let-inv (`let p ∷= t `in u) = , , , t , p , u

prd⊗-inv :
  {n : ℕ} {γ : Context n} {t u : Check n} {Γ Δ : Usages γ} {σ τ : Type} →
  Γ ⊢ σ ⊗ τ ∋ `prd t u ⊠ Δ → Σ[ θ ∈ Usages γ ] Γ ⊢ σ ∋ t ⊠ θ × θ ⊢ τ ∋ u ⊠ Δ
prd⊗-inv (`prd⊗ t u) = , t , u

prd&-inv :
  {n : ℕ} {γ : Context n} {t u : Check n} {Γ Δ : Usages γ} {σ τ : Type} →
  Γ ⊢ σ & τ ∋ `prd t u ⊠ Δ → Γ ⊢ σ ∋ t ⊠ Δ × Γ ⊢ τ ∋ u ⊠ Δ
prd&-inv (`prd& t u) = t , u

-- useful corrolaries
app-inv-function : 
  {n : ℕ} {γ : Context n} {t : Infer n} {u : Check n} {Γ Δ : Usages γ} {τ : Type} →
  (p : Γ ⊢ `app t u ∈ τ ⊠ Δ) → let (θ , σ , _) = app-inv p in Γ ⊢ t ∈ σ ─o τ ⊠ θ
app-inv-function p = let (_ , _ , T , _) = app-inv p in T

app-inv-argument : 
  {n : ℕ} {γ : Context n} {t : Infer n} {u : Check n} {Γ Δ : Usages γ} {τ : Type} →
  (p : Γ ⊢ `app t u ∈ τ ⊠ Δ) → let (θ , σ , _) = app-inv p in θ ⊢ σ ∋ u ⊠ Δ
app-inv-argument p = let (_ , _ , _ , U) = app-inv p in U

case-inv-scrutinee : 
  {n : ℕ} {γ : Context n} {t : Infer n} {l r : Check (suc n)} {Γ Δ : Usages γ} {ν₁ ν₂ : Type} →
  (p : Γ ⊢ `case t return ν₁ of l %% r ∈ ν₂ ⊠ Δ) →
  let (θ , σ , τ , _) = case-inv p in Γ ⊢ t ∈ σ ⊕ τ ⊠ θ
case-inv-scrutinee p = let (_ , _ , _ , T , _) = case-inv p in T

case-inv-left : 
  {n : ℕ} {γ : Context n} {t : Infer n} {l r : Check (suc n)} {Γ Δ : Usages γ} {ν₁ ν₂ : Type} →
  (p : Γ ⊢ `case t return ν₁ of l %% r ∈ ν₂ ⊠ Δ) →
  let (θ , σ , τ , _) = case-inv p in [ σ ] ∷ θ ⊢ ν₁ ∋ l ⊠ ] σ [ ∷ Δ
case-inv-left p = let (_ , _ , _ , _ , L , _) = case-inv p in L

case-inv-right : 
  {n : ℕ} {γ : Context n} {t : Infer n} {l r : Check (suc n)} {Γ Δ : Usages γ} {ν₁ ν₂ : Type} →
  (p : Γ ⊢ `case t return ν₁ of l %% r ∈ ν₂ ⊠ Δ) →
  let (θ , σ , τ , _) = case-inv p in [ τ ] ∷ θ ⊢ ν₁ ∋ r ⊠ ] τ [ ∷ Δ
case-inv-right p = let (_ , _ , _ , _ , _ , R) = case-inv p in R

let-inv-bound : 
  {n o : ℕ} {γ : Context n} {p : Pattern o} {t : Infer n} {u : Check (o + n)}
  {Γ Δ : Usages γ} {τ : Type} (p : Γ ⊢ τ ∋ `let p ∷= t `in u ⊠ Δ) →
  let (θ , σ , _) = let-inv p in Γ ⊢ t ∈ σ ⊠ θ
let-inv-bound p = let (_ , _ , _ , T , _) = let-inv p in T

let-inv-pattern : 
  {n o : ℕ} {γ : Context n} {p : Pattern o} {t : Infer n} {u : Check (o + n)}
  {Γ Δ : Usages γ} {τ : Type} (d : Γ ⊢ τ ∋ `let p ∷= t `in u ⊠ Δ) →
  let (_ , σ , δ , _) = let-inv d in σ ∋ p ↝ δ
let-inv-pattern p = let (_ , _ , _ , _ , P , _) = let-inv p in P

let-inv-body : 
  {n o : ℕ} {γ : Context n} {p : Pattern o} {t : Infer n} {u : Check (o + n)}
  {Γ Δ : Usages γ} {τ : Type} (p : Γ ⊢ τ ∋ `let p ∷= t `in u ⊠ Δ) →
  let (θ , σ , δ , _) = let-inv p in [[ δ ]] ++ θ ⊢ τ ∋ u ⊠ ]] δ [[ ++ Δ
let-inv-body p = let (_ , _ , _ , _ , _ , U) = let-inv p in U

prd-inv-fst : 
  {n : ℕ} {γ : Context n} {t u : Check n} {Γ Δ : Usages γ} {σ τ : Type} →
  (p : Γ ⊢ σ ⊗ τ ∋ `prd t u ⊠ Δ) → let (θ , _) = prd⊗-inv p in Γ ⊢ σ ∋ t ⊠ θ
prd-inv-fst p = let (_ , T , _) = prd⊗-inv p in T

prd-inv-snd : 
  {n : ℕ} {γ : Context n} {t u : Check n} {Γ Δ : Usages γ} {σ τ : Type} →
  (p : Γ ⊢ σ ⊗ τ ∋ `prd t u ⊠ Δ) → let (θ , _) = prd⊗-inv p in θ ⊢ τ ∋ u ⊠ Δ
prd-inv-snd p = let (_ , _ , U) = prd⊗-inv p in U
