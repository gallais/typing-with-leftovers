module linear.Typing.Consumption where

open import Data.Nat
open import Data.Vec hiding (_++_)
open import Data.Product
open import Function

open import linear.Type
open import linear.Context hiding (_++_)
open import linear.Typing
open import linear.Usage hiding ([_] ; _++_)
open import linear.Usage.Consumption
import Relation.Binary.PropositionalEquality as PEq

mutual

  consumptionInfer : Consumption TInfer
  consumptionInfer (`var k)                     = consumptionFin k
  consumptionInfer (`app t u)                   = trans (consumptionInfer t) (consumptionCheck u)
  consumptionInfer (`fst t)                     = consumptionInfer t
  consumptionInfer (`snd t)                     = consumptionInfer t
  consumptionInfer (`case t return σ of l %% r) =
    trans (consumptionInfer t) $ truncate [ _ ] $ consumptionCheck l
  consumptionInfer (`exfalso σ t)               = consumptionInfer t
  consumptionInfer (`cut t)                     = consumptionCheck t

  consumptionCheck : Consumption TCheck
  consumptionCheck (`lam t)            = truncate [ _ ] $ consumptionCheck t
  consumptionCheck (`let p ∷= t `in u) =
    trans (consumptionInfer t) $ truncate (patternContext p) $ consumptionCheck u
  consumptionCheck `unit               = refl _
  consumptionCheck (`prd⊗ a b)         = trans (consumptionCheck a) (consumptionCheck b)
  consumptionCheck (`prd& a b)         = consumptionCheck a
  consumptionCheck (`inl t)            = consumptionCheck t
  consumptionCheck (`inr t)            = consumptionCheck t
  consumptionCheck (`neu t)            = consumptionInfer t

mutual

  framingInfer : Framing TInfer
  framingInfer c (`var k)                     = `var (framingFin c k)
  framingInfer c (`app t u)                   =
    let (_ , c₁ , c₂) = divide c (consumptionInfer t) (consumptionCheck u)
    in `app (framingInfer c₁ t) (framingCheck c₂ u)
  framingInfer c (`fst t)    = `fst framingInfer c t
  framingInfer c (`snd t)    = `snd framingInfer c t
  framingInfer c (`case t return σ of l %% r) =
    let (_ , c₁ , c₂) = divide c (consumptionInfer t) (truncate [ _ ] (consumptionCheck l))
    in `case framingInfer c₁ t return σ of framingCheck (_ ∷ c₂) l %% framingCheck (_ ∷ c₂) r
  framingInfer c (`exfalso σ t) = `exfalso σ (framingInfer c t)
  framingInfer c (`cut t)       = `cut (framingCheck c t)

  framingCheck : Framing TCheck
  framingCheck c (`lam t)            = `lam framingCheck (_ ∷ c) t
  framingCheck c (`let p ∷= t `in u) =
    let (_ , c₁ , c₂) = divide c (consumptionInfer t) (truncate (patternContext p) (consumptionCheck u))
    in `let p ∷= framingInfer c₁ t `in framingCheck (pure (patternContext p) ++ c₂) u
  framingCheck c `unit               = PEq.subst (TCheck _ _ _) (equality c) `unit
  framingCheck c (`prd⊗ a b)         =
    let (_ , c₁ , c₂) = divide c (consumptionCheck a) (consumptionCheck b)
    in  `prd⊗ (framingCheck c₁ a) (framingCheck c₂ b)
  framingCheck c (`prd& a b)         = `prd& (framingCheck c a) (framingCheck c b)
  framingCheck c (`inl t)            = `inl framingCheck c t
  framingCheck c (`inr t)            = `inr framingCheck c t
  framingCheck c (`neu t)            = `neu framingInfer c t
