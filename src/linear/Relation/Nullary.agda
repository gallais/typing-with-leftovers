module linear.Relation.Nullary where

open import Data.Bool
open import Relation.Nullary

isYes : ∀ {ℓ} {P : Set ℓ} → Dec P → Bool
isYes (yes _) = true
isYes (no  _) = false

fromYes : ∀ {ℓ} {P : Set ℓ} (d : Dec P) {_ : T (isYes d)} → P
fromYes (yes p) = p
fromYes (no ¬p) {()}
