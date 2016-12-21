module linear.Main where

open import Level
open import linear.Surface.Surface
open import linear.Data.ByteString
open import Data.String
open import Data.List hiding (_++_)
open import Function
open import Coinduction
open import IO

open import Data.Maybe
open import linear.Type

data Pair {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  _,_ : A → B → Pair A B
{-# HASKELL type AgdaPair l1 l2 a b = (a,b) #-}
{-# COMPILED_DATA Pair MAlonzo.Code.Qlinear.Main.AgdaPair (,) #-}


uncurry : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
          (A → B → C) → (Pair A B → C)
uncurry f (a , b) = f a b

postulate
  parseProblem  : ByteString → Maybe (Pair Type Check)
  parseProblems : ByteString → Maybe (List (Pair Type Check))

{-# IMPORT Surface.Parser #-}
{-# COMPILED parseProblem  Surface.Parser.parseProblem  #-}
{-# COMPILED parseProblems Surface.Parser.parseProblems #-}

infixr 5 _¡[_]_
_¡[_]_ : ∀ {ℓ} {A : Set ℓ} → Maybe A → String → (A → _) → _
ma ¡[ str ] f = maybe f (♯ putStrLn ("Fail: " ++ str)) ma

main =
  run $ ♯ lift (readFileBS "input.lin") >>= λ bs →
        parseProblems bs ¡[ "parse" ] foldr (uncurry λ σ c io →
        ♯ ((linear σ c      ¡[ "check" ] λ _ → ♯ putStrLn "Success") >> io)) (♯ return _)
