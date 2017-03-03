module linear.Main where

open import Level
open import linear.Surface.Surface
open import linear.Data.ByteString
open import Data.String
open import Data.List as List hiding (_++_)
open import Function
open import Coinduction
open import IO

open import Data.Maybe as Maybe
open import linear.Type

data Pair {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  _,_ : A → B → Pair A B
{-# FOREIGN GHC type AgdaPair l1 l2 a b = (a,b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Qlinear.Main.AgdaPair ((,)) #-}

Pairmap : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
          (A → C) → (B → D) → Pair A B → Pair C D
Pairmap f g (a , b) = f a , g b

uncurry : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
          (A → B → C) → (Pair A B → C)
uncurry f (a , b) = f a b

postulate
  RparseProblems : RByteString → Maybe (List (Pair RType RCheck))

{-# FOREIGN GHC import qualified Data.ByteString #-}
{-# FOREIGN GHC import qualified Type.Parser     #-}
{-# FOREIGN GHC import qualified Surface.Parser  #-}
{-# COMPILE GHC RparseProblems = Surface.Parser.parseProblems #-}

parseProblems : ByteString → Maybe (List (Pair Type Check))
parseProblems bs = Maybe.map (List.map (Pairmap embed^RType embed^RCheck)) $ RparseProblems bs

infixr 5 _¡[_]_
_¡[_]_ : ∀ {ℓ} {A : Set ℓ} → Maybe A → String → (A → _) → _
ma ¡[ str ] f = maybe f (♯ putStrLn ("Fail: " ++ str)) ma

main =
  run $ ♯ lift (readFileBS "input.lin") >>= λ bs →
        parseProblems bs ¡[ "parse" ] foldr (uncurry λ σ c io →
        ♯ ((linear σ c      ¡[ "check" ] λ _ → ♯ putStrLn "Success") >> io)) (♯ return _)
