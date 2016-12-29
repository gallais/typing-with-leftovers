{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveTraversable #-}

module Type.Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.List (elemIndex)
import Data.Attoparsec.ByteString
import Data.Attoparsec.Combinator
import Data.Attoparsec.ByteString.Char8 as AC (char, satisfy, skipSpace)

data TypeF b =
    Base   b
  | Unit
  | Tensor (TypeF b) (TypeF b)
  | Plus   (TypeF b) (TypeF b)
  | With   (TypeF b) (TypeF b)
  | Lolli  (TypeF b) (TypeF b)
  deriving (Show, Functor, Foldable, Traversable)

type RType = TypeF String
type Type  = TypeF Integer

two :: TypeF b
two = Plus Unit Unit

pBase :: Parser String
pBase = string "'" *> many1 (AC.satisfy (`elem` ['a'..'z']))

-- Because the grammar is left-recursive, we need to break it
-- in various fixity-based tiers to avoid infinite loops

betweenSpace :: Parser a -> Parser a
betweenSpace p = skipSpace *> p <* skipSpace

pRType5 :: Parser RType
pRType5 = Lolli <$> pRType6
               <*> (betweenSpace (string "-o") *> pRType5)
     <|> pRType6

pRType6 :: Parser RType
pRType6 = Tensor <$> pRType7
                <*> (betweenSpace (string "*") *> pRType6)
     <|> pRType7

pRType7 :: Parser RType
pRType7 = Plus <$> pRType8
              <*> (betweenSpace (string "+") *> pRType7)
     <|> pRType8

pRType8 :: Parser RType
pRType8 = With <$> pRType9
              <*> (betweenSpace (string "&") *> pRType8)
     <|> pRType9

pRType9 :: Parser RType
pRType9 = Base <$> pBase
     <|> Unit <$ string "1"
     <|> two  <$ string "2"
     <|> string "(" *> pRType <* string ")"

pRType :: Parser RType
pRType = pRType5

reifyNames :: (Traversable f, Eq a) => Parser (f a) -> Parser (f Integer)
reifyNames = fmap $ (`evalState` (0, [])) . traverse reifyName where

  reifyName :: Eq a => a -> State (Int, [a]) Integer
  reifyName x = fromIntegral <$> do
    (n, xs) <- get
    case elemIndex x xs of
      Just k  -> return (n - 1 - k)
      Nothing -> put (n+1, x:xs) >> return n
