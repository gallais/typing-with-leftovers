{-# LANGUAGE OverloadedStrings #-}

module Type.Parser where

import Control.Applicative
import Control.Monad
import Data.ByteString
import Data.Attoparsec.ByteString
import Data.Attoparsec.Combinator
import Data.Attoparsec.ByteString.Char8

data Type =
    Base   !Integer
  | Tensor Type Type
  | Plus   Type Type
  | Lolli  Type Type
  deriving Show

pBase :: Parser Integer
pBase = decimal >>= \ i -> i <$ guard (0 <= i)

-- Because the grammar is left-recursive, we need to break it
-- in various fixity-based tiers to avoid infinite loops

betweenSpace :: Parser a -> Parser a
betweenSpace p = skipSpace *> p <* skipSpace

pType5 :: Parser Type
pType5 = Lolli <$> pType6
               <*> (betweenSpace (string "-o") *> pType5)
     <|> pType6

pType6 :: Parser Type
pType6 = Tensor <$> pType7
                <*> (betweenSpace (string "*") *> pType6)
     <|> pType7

pType7 :: Parser Type
pType7 = Plus <$> pType8
              <*> (betweenSpace (string "+") *> pType7)
     <|> pType8

pType8 :: Parser Type
pType8 = Base <$> pBase
     <|> string "(" *> pType <* string ")"

pType :: Parser Type
pType = pType5

