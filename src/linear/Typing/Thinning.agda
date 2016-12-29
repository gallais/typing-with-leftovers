module linear.Typing.Thinning where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.Product as P
open import Data.Vec hiding (map ; tail)
open import Function
open import Relation.Binary.PropositionalEquality as PEq

open import linear.Type
open import linear.Scope as Sc
open import linear.Context as C
open import linear.Language
import linear.Context.Pointwise as CP
open import linear.Usage as U hiding (tail)
open import linear.Usage.Consumption hiding (refl ; trans)
import linear.Usage.Pointwise as UP
open import linear.Usage.Erasure
open import linear.Language
open import linear.Typing as T
open import linear.Typing.Consumption
open import linear.Typing.Extensional

Thinning : {T : ℕ → Set} (Wk : Sc.Weakening T) (𝓣 : Typing T) → Set
Thinning {T} Wk 𝓣 =
  {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} (𝓜 : U.Mergey M) →
  {γ : Context k} (Γ Δ : Usages γ) {t : T l} {σ : Type} →
  𝓣 (Γ U.⋈ 𝓜) t σ (Δ U.⋈ 𝓜) → Σ[ t′ ∈ T k ] t ≡ Wk m t′ × 𝓣 Γ t′ σ Δ

data Usages[_]
  {ℓ^R : Level} (R : {σ : Type} (S T : Usage σ) → Set ℓ^R) :
  {k : ℕ} {γ : Context k} → Usages γ → Usages γ → Set ℓ^R where
  []  : Usages[ R ] [] []
  _∷_ : {k : ℕ} {γ : Context k} {Γ Δ : Usages γ} {σ : Type} {S T : Usage σ} →
        R S T → Usages[ R ] Γ Δ → Usages[ R ] (S ∷ Γ) (T ∷ Δ)

reflUsages : {k : ℕ} {γ : Context k} (Γ : Usages γ) → Usages[ _≡_ ] Γ Γ
reflUsages []      = []
reflUsages (x ∷ Γ) = refl ∷ reflUsages Γ

equalUsages : {k : ℕ} {γ : Context k} {Γ Δ : Usages γ} → Usages[ _≡_ ] Γ Δ → Γ ≡ Δ
equalUsages []           = refl
equalUsages (refl ∷ eqs) = cong (_∷_ _) (equalUsages eqs)

Thinning′ : {T : ℕ → Set} (Wk : Sc.Weakening T) (𝓣 : Typing T) → Set
Thinning′ {T} Wk 𝓣 =
  {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} (𝓜 : U.Mergey M) →
  {γ : Context k} {Γ Δ : Usages γ} {ξ ζ : Usages (γ C.⋈ M)} {t : T l} {σ : Type} →
  Usages[ _≡_ ] ξ (Γ U.⋈ 𝓜) → Usages[ _≡_ ] ζ (Δ U.⋈ 𝓜) →
  𝓣 ξ t σ ζ → Σ[ t′ ∈ T k ] t ≡ Wk m t′ × 𝓣 Γ t′ σ Δ

thinning : {T : ℕ → Set} {Wk : Sc.Weakening T} {𝓣 : Typing T} →
           Thinning′ Wk 𝓣 → Thinning Wk 𝓣
thinning th 𝓜 Γ Δ t = th 𝓜 (reflUsages _) (reflUsages _) t

thinning′Fin : Thinning′ Sc.weakFin TFin
thinning′Fin finish Γ Δ k rewrite equalUsages Γ | equalUsages Δ = , refl , k
thinning′Fin (copy 𝓜) {γ = σ ∷ γ} {Γ = _ ∷ Γ} {Δ = _ ∷ Δ} (refl ∷ eqΓ) (refl ∷ eqΔ) z
  rewrite ⋈ˡ-injective (_ , _ , _ , _ , _ , 𝓜 , _) (equalUsages eqΓ) (equalUsages eqΔ) =
  Fin.zero , refl , z
thinning′Fin (copy 𝓜) {γ = σ ∷ γ} {S ∷ Γ} {T ∷ Δ} (eqS ∷ eqΓ) (eqT ∷ eqΔ) (s k)
  rewrite trans (PEq.sym eqS) eqT =
  let (k′ , eq , K) = thinning′Fin 𝓜 eqΓ eqΔ k
  in Fin.suc k′ , cong Fin.suc eq , s K
thinning′Fin (insert A 𝓜) (S ∷ Γ) (T ∷ Δ) (s k) =
  let (k′ , eq , K) = thinning′Fin 𝓜 Γ Δ k
  in k′ , cong Fin.suc eq , K
thinning′Fin (insert A 𝓜) (S ∷ Γ) (T ∷ Δ) z = case trans S (PEq.sym T) of λ ()

thinningFin : Thinning Sc.weakFin TFin
thinningFin = thinning thinning′Fin 

split-⋈ : 
  {k l : ℕ} {m : Sc.Mergey k l} {M : C.Mergey m} (𝓜 : U.Mergey M) →
  {γ : Context k} {Γ Δ : Usages γ} {ξ Φ ζ : Usages (γ C.⋈ M)} →
  Usages[ _≡_ ] ξ (Γ U.⋈ 𝓜) → Usages[ _≡_ ] ζ (Δ U.⋈ 𝓜) →
  ξ ⊆ Φ → Φ ⊆ ζ → ∃ λ φ → Usages[ _≡_ ] Φ (φ U.⋈ 𝓜)
split-⋈ finish        eq₁ eq₂ le₁ le₂ = , reflUsages _
split-⋈ (copy 𝓜) {σ ∷ γ} {S ∷ Γ} {T ∷ Δ} (eqS ∷ eq₁) (eqT ∷ eq₂) (─∷ le₁) (─∷ le₂) =
  let (φ , eq) = split-⋈ 𝓜 eq₁ eq₂ le₁ le₂
  in T ∷ φ , eqT ∷ eq
split-⋈ (copy 𝓜) {.σ ∷ γ} {S ∷ Γ} {T ∷ Δ} (eqS ∷ eq₁) (eqT ∷ eq₂) (─∷ le₁) (σ ∷ le₂) =
  let (φ , eq) = split-⋈ 𝓜 eq₁ eq₂ le₁ le₂
  in Usage.[ σ ] ∷ φ , refl ∷ eq
split-⋈ (copy 𝓜) {.σ ∷ γ} {S ∷ Γ} {T ∷ Δ} (eqS ∷ eq₁) (eqT ∷ eq₂) (σ ∷ le₁) (─∷ le₂) =
  let (φ , eq) = split-⋈ 𝓜 eq₁ eq₂ le₁ le₂
  in ] σ [ ∷ φ , refl ∷ eq
split-⋈ (insert A 𝓜) (eqA ∷ eq₁) (_ ∷ eq₂) (─∷ le₁) (─∷ le₂) =
  let (φ , eq) = split-⋈ 𝓜 eq₁ eq₂ le₁ le₂
  in , eqA ∷ eq
split-⋈ (insert A 𝓜) (eqA ∷ eq₁) (_ ∷ eq₂) (─∷ le₁) (a ∷ le₂) =
  let (φ , eq) = split-⋈ 𝓜 eq₁ eq₂ le₁ le₂
  in , eqA ∷ eq
split-⋈ (insert A 𝓜) (_ ∷ eq₁) (eqA ∷ eq₂) (a ∷ le₁) (─∷ le₂) =
  let (φ , eq) = split-⋈ 𝓜 eq₁ eq₂ le₁ le₂
  in , eqA ∷ eq

thinning′Infer : Thinning′ weakInfer TInfer
thinning′Check : Thinning′ weakCheck TCheck

thinning′Infer 𝓜 eq₁ eq₂ (`var k) =
  let (k′ , eq , K) = thinning′Fin 𝓜 eq₁ eq₂ k
  in `var k′ , cong `var_ eq , `var K
thinning′Infer 𝓜 eq₁ eq₂ (`app f t) =
  let (φ , eq)       = split-⋈ 𝓜 eq₁ eq₂ (consumptionInfer f) (consumptionCheck t)
      (f′ , eqf , F) = thinning′Infer 𝓜 eq₁ eq f
      (t′ , eqt , T) = thinning′Check 𝓜 eq eq₂ t
  in , cong₂ `app eqf eqt , `app F T
thinning′Infer 𝓜 eq₁ eq₂ (`skip u t) =
  let (φ , eq)       = split-⋈ 𝓜 eq₁ eq₂ (consumptionCheck u) (consumptionInfer t)
      (u′ , equ , U) = thinning′Check 𝓜 eq₁ eq u
      (t′ , eqt , T) = thinning′Infer 𝓜 eq eq₂ t
  in , cong₂ `skip equ eqt , `skip U T
thinning′Infer 𝓜 eq₁ eq₂ (`fst t) =
  let (t′ , eqt , T) = thinning′Infer 𝓜 eq₁ eq₂ t
  in , cong `fst_ eqt , `fst T
thinning′Infer 𝓜 eq₁ eq₂ (`snd t) =
  let (t′ , eqt , T) = thinning′Infer 𝓜 eq₁ eq₂ t
  in , cong `snd_ eqt , `snd T
thinning′Infer 𝓜 eq₁ eq₂ (`case t return σ of l %% r) =
  let (φ , eq)       = split-⋈ 𝓜 eq₁ eq₂ (consumptionInfer t) (tail (consumptionCheck l))
      (t′ , eqt , T) = thinning′Infer 𝓜 eq₁ eq t
      (l′ , eql , L) = thinning′Check (copy 𝓜) (refl ∷ eq) (refl ∷ eq₂) l
      (r′ , eqr , R) = thinning′Check (copy 𝓜) (refl ∷ eq) (refl ∷ eq₂) r
  in , cong₂ (λ t → uncurry (`case t return σ of_%%_)) eqt (cong₂ _,_ eql eqr)
     , `case T return σ of L %% R
thinning′Infer 𝓜 eq₁ eq₂ (`cut t) = 
  let (t′ , eqt , T) = thinning′Check 𝓜 eq₁ eq₂ t
  in , cong (λ t → `cut t _) eqt , `cut T

thinning′Check 𝓜 eq₁ eq₂ (`lam t) =
  let (t′ , eqt , T) = thinning′Check (copy 𝓜) (refl ∷ eq₁) (refl ∷ eq₂) t
  in , cong `lam_ eqt , `lam T
thinning′Check 𝓜 eq₁ eq₂ (`let p ∷= t `in u) =
  let o              = T.patternSize p
      δ              = patternContext p
      Φ              = inferOutput t
      (φ , eq)       = split-⋈ 𝓜 eq₁ eq₂ (consumptionInfer t)
                     $ truncate δ (consumptionCheck u)
      (t′ , eqt , T) = thinning′Infer 𝓜 eq₁ eq t
      v              : ([[ δ ]] U.++ φ) U.⋈ U.copys o 𝓜
                       ⊢ _ ∋ _
                       ⊠ (]] δ [[ U.++ _) U.⋈ U.copys o 𝓜
      v              = extensionalCheck (CP.copys δ) (CP.sym $ CP.copys δ)
                       (UP.irrelevance _ $ UP.trans (UP.copys [[ δ ]])
                        (UP.refl {Γ = [[ δ ]]} UP.++ UP.fromEq (PEq.sym $ equalUsages eq)))
                       (UP.irrelevance _ $ UP.trans
                        (UP.refl {Γ = ]] δ [[} UP.++ UP.fromEq (equalUsages eq₂))
                        (UP.sym (UP.copys ]] δ [[)))
                       u
      (u′ , equ , U) = thinning′Check (U.copys o 𝓜) (reflUsages _) (reflUsages _) v
  in , cong₂ (`let _ ∷=_`in_) eqt equ , `let p ∷= T `in U
thinning′Check 𝓜 eq₁ eq₂ `unit =
  let eq = ⋈ˡ-injective (_ , _ , _ , _ , _ , 𝓜 , _) (equalUsages eq₁) (equalUsages eq₂)
  in , refl , subst (TCheck _ _ _) eq `unit
thinning′Check 𝓜 eq₁ eq₂ (`prd⊗ a b) =
  let (φ , eq)       = split-⋈ 𝓜 eq₁ eq₂ (consumptionCheck a) (consumptionCheck b)
      (a′ , eqa , A) = thinning′Check 𝓜 eq₁ eq a
      (b′ , eqb , B) = thinning′Check 𝓜 eq eq₂ b
  in , cong₂ `prd eqa eqb , `prd⊗ A B
thinning′Check 𝓜 eq₁ eq₂ (`prd& a b) =
  let (a′ , eqa , A) = thinning′Check 𝓜 eq₁ eq₂ a
      (b′ , eqb , B) = thinning′Check 𝓜 eq₁ eq₂ b
  in , cong₂ `prd eqa eqb , `prd& A B
thinning′Check 𝓜 eq₁ eq₂ (`inl t) =
  let (t′ , eqt , T) = thinning′Check 𝓜 eq₁ eq₂ t
  in , cong `inl_ eqt , `inl T
thinning′Check 𝓜 eq₁ eq₂ (`inr t) =
  let (t′ , eqt , T) = thinning′Check 𝓜 eq₁ eq₂ t
  in , cong `inr_ eqt , `inr T
thinning′Check 𝓜 eq₁ eq₂ (`neu t) =
  let (t′ , eqt , T) = thinning′Infer 𝓜 eq₁ eq₂ t
  in , cong `neu_ eqt , `neu T

thinningInfer : Thinning weakInfer TInfer
thinningInfer = thinning thinning′Infer

thinningCheck : Thinning weakCheck TCheck
thinningCheck = thinning thinning′Check

-- A more conventional formulation of Thinning for Check and Infer
-- can be derived as simple corrolaries of previous results:

thinCheck :
  {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {t : Check n} {σ : Type} → Γ ⊢ σ ∋ t ⊠ Δ →
  Σ[ k ∈ ℕ ] Σ[ δ ∈ Context k ] Σ[ t′ ∈ Check k ] Σ[ m ∈ Sc.Mergey k n ]
  t ≡ weakCheck m t′ × [[ δ ]] ⊢ σ ∋ t′ ⊠ ]] δ [[
thinCheck T =
  let (k , m , δ , M , 𝓜 , eqs , eq) = ⌊ consumptionCheck T ⌋
      EQs = (UP.irrelevance _ (UP.coerceˡ eqs))
      T₁  = extensionalCheck (CP.sym eqs) eqs EQs (UP.coerceʳ eqs) T
      T₂  = framingCheck eq T₁
      (t′ , eq , T₃) = thinningCheck 𝓜 _ _ T₂
  in k , δ , t′ , m , eq , T₃

thinInfer :
  {n : ℕ} {γ : Context n} {Γ Δ : Usages γ} {t : Infer n} {σ : Type} → Γ ⊢ t ∈ σ ⊠ Δ →
  Σ[ k ∈ ℕ ] Σ[ δ ∈ Context k ] Σ[ t′ ∈ Infer k ] Σ[ m ∈ Sc.Mergey k n ]
  t ≡ weakInfer m t′ × [[ δ ]] ⊢ t′ ∈ σ ⊠ ]] δ [[
thinInfer T =
  let (k , m , δ , M , 𝓜 , eqs , eq) = ⌊ consumptionInfer T ⌋
      EQs = (UP.irrelevance _ (UP.coerceˡ eqs))
      T₁  = extensionalInfer (CP.sym eqs) eqs EQs (UP.coerceʳ eqs) T
      T₂  = framingInfer eq T₁
      (t′ , eq , T₃) = thinningInfer 𝓜 _ _ T₂
  in k , δ , t′ , m , eq , T₃
