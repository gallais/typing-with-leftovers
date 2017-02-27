module linear.Surface.Surface where

open import Data.Maybe
open import Data.String using (String)
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_] ; _⊛_ ; _>>=_)
open import Data.Empty
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])

open import linear.Type

{-# IMPORT Surface.Parser #-}

data Pattern : Set where
  `v   : String → Pattern
  _,,_ : (p q : Pattern) → Pattern
{-# COMPILED_DATA Pattern Surface.Parser.Pattern Surface.Parser.All Surface.Parser.And #-}

data Check : Set
{-# COMPILED_DECLARE_DATA Check Surface.Parser.Check #-}
data Infer : Set
{-# COMPILED_DECLARE_DATA Infer Surface.Parser.Infer #-}

data Check where
  `lam_↦_      : String → Check → Check
  `let_∷=_`in_ : Pattern → Infer → Check → Check
  `unit        : Check
  `prd         : Check → Check → Check
  `inl_        : Check → Check
  `inr_        : Check → Check
  `neu_        : Infer → Check
{-# COMPILED_DATA
    Check Surface.Parser.Check
    Surface.Parser.Lam
    Surface.Parser.Let
    Surface.Parser.One
    Surface.Parser.Prd
    Surface.Parser.Inl
    Surface.Parser.Inr
    Surface.Parser.Neu
 #-}

data Infer where
  `var                    : String → Infer
  `app                    : Infer → Check → Infer
  `skip                   : Check → Infer → Infer
  `fst `snd               : Infer → Infer
  `case_return_of_↦_%%_↦_ : Infer → Type → String → Check → String → Check → Infer
  `cut                    : Check → Type → Infer
{-# COMPILED_DATA
    Infer Surface.Parser.Infer
    Surface.Parser.Var
    Surface.Parser.App
    Surface.Parser.Skp
    Surface.Parser.Fst
    Surface.Parser.Snd
    Surface.Parser.Cas
    Surface.Parser.Cut
#-}

-- example:

`swap⊗ : Check
`swap⊗ = `lam "pair" ↦
         `let `v "left" ,, `v "right" ∷= `var "pair"
         `in `prd (`neu `var "right") (`neu `var "left")

`swap⊕ : (σ τ : Type) → Check
`swap⊕ σ τ = `lam "sum" ↦ `neu
             `case (`var "sum") return τ ⊕ σ
             of "left"  ↦ `inr (`neu `var "left")
             %% "right" ↦ `inl (`neu `var "right")


`swap& : Check
`swap& = `lam "pair" ↦
         `prd (`neu (`snd (`var "pair"))) (`neu (`fst (`var "pair")))



-----------------------------------------------
-- Scope Checking
-----------------------------------------------

infix 1 _⁇_↝_
data _⁇_↝_ {A : Set} : ∀ {n} → Vec A n → A → Fin n → Set where
  ze : ∀ {n} {xs : Vec A n} {x : A} → x ∷ xs ⁇ x ↝ zero
  su : ∀ {n} {xs : Vec A n} {x y : A} {k : Fin n} →
       x ≢ y → xs ⁇ x ↝ k → y ∷ xs ⁇ x ↝ suc k

⁇↝-invert : ∀ {A} {n} {xs : Vec A n} {x y} {k} → y ∷ xs ⁇ x ↝ k →
            x ≡ y ⊎ ∃ λ k → xs ⁇ x ↝ k
⁇↝-invert ze          = inj₁ refl
⁇↝-invert (su ¬eq pr) = inj₂ (, pr)

module withEqDec {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) where

  resolve : ∀ {n} (x : A) (xs : Vec A n) → Dec (∃ λ k → xs ⁇ x ↝ k)
  resolve x []       = no (λ { (() , ()) })
  resolve x (y ∷ xs) with eq? x y | resolve x xs
  resolve x (.x ∷ xs) | yes refl | _ = yes (, ze)
  ... | no ¬eq | yes (k , pr) = yes (, su ¬eq pr) 
  ... | no ¬eq | no ¬pr = no ([ ¬eq , ¬pr ] ∘ ⁇↝-invert ∘ proj₂)

open withEqDec Data.String._≟_
import linear.Language as L
open import Category.Monad
import Level
open RawMonad (monad {Level.zero}) hiding (_⊗_)

scopePattern : Pattern → ∃ λ n → Vec String n × L.Pattern n
scopePattern (`v nm)   = , nm ∷ [] , L.`v
scopePattern (p ,, q) =
  let (m , xs , p′) = scopePattern p
      (n , ys , q′) = scopePattern q
  in , xs ++ ys , p′ L.,, q′

mutual

  scopeCheck : ∀ {n} → Vec String n → Check → Maybe (L.Check n)
  scopeCheck nms (`lam nm ↦ b) = L.`lam_ <$> scopeCheck (nm ∷ nms) b
  scopeCheck nms (`let p ∷= t `in u) =
    let (m , nms′ , p′) = scopePattern p
    in L.`let p′ ∷=_`in_ <$> scopeInfer nms t ⊛ scopeCheck (nms′ ++ nms) u
  scopeCheck nms `unit      = return L.`unit
  scopeCheck nms (`prd a b) = L.`prd <$> scopeCheck nms a ⊛ scopeCheck nms b
  scopeCheck nms (`inl t) = L.`inl_ <$> scopeCheck nms t
  scopeCheck nms (`inr t) = L.`inr_ <$> scopeCheck nms t
  scopeCheck nms (`neu i) = L.`neu_ <$> scopeInfer nms i

  scopeInfer : ∀ {n} → Vec String n → Infer → Maybe (L.Infer n)
  scopeInfer nms (`var nm) with resolve nm nms
  ... | yes (k , _) = just (L.`var k)
  ... | no ¬p = nothing
  scopeInfer nms (`app f t)  = L.`app  <$> scopeInfer nms f ⊛ scopeCheck nms t
  scopeInfer nms (`skip u t) = L.`skip <$> scopeCheck nms u ⊛ scopeInfer nms t
  scopeInfer nms (`fst t)    = L.`fst_ <$> scopeInfer nms t
  scopeInfer nms (`snd t)    = L.`snd_ <$> scopeInfer nms t
  scopeInfer nms (`case i return σ of nml ↦ l %% nmr ↦ r) =
    L.`case_return σ of_%%_ <$> scopeInfer nms i ⊛ scopeCheck (nml ∷ nms) l ⊛ scopeCheck (nmr ∷ nms) r
  scopeInfer nms (`cut t σ) = (λ t → L.`cut t σ) <$> scopeCheck nms t



-----------------------------------------------
-- Scope and Type Checking
-----------------------------------------------

import linear.Usage as U
import linear.Typing as T
import linear.Typecheck as TC
import linear.Typecheck.Problem as TCP

linear : (σ : Type) (t : Check) → Maybe (∃ λ c → just c ≡ scopeCheck [] t
                                               × U.[] T.⊢ σ ∋ c ⊠ U.[])
linear σ c with scopeCheck [] c
... | nothing = nothing
... | just t  = case TC.check U.[] σ t of λ
              { (yes (U.[] TCP., pr)) → just (t , refl , pr)
              ; (no ¬C)               → nothing
              }

-- example:
`swap⊗-ok : ∀ σ τ → Is-just (linear ((σ ⊗ τ) ─o (τ ⊗ σ)) `swap⊗)
`swap⊗-ok σ τ rewrite eq-diag τ | eq-diag σ = just _

-- example:
`swap⊕-ok : ∀ σ τ → Is-just (linear ((σ ⊕ τ) ─o (τ ⊕ σ)) (`swap⊕ σ τ))
`swap⊕-ok σ τ rewrite eq-diag τ | eq-diag σ | eq-diag (τ ⊕ σ) = just _

-- example:
`swap&-ok : ∀ σ τ → Is-just (linear ((σ & τ) ─o (τ & σ)) `swap&)
`swap&-ok σ τ rewrite eq-diag τ | eq-diag σ = just _