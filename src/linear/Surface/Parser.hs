{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveTraversable #-}

module Surface.Parser where

import Type.Parser
import Data.Text

import Control.Applicative
import Control.Monad
import Data.ByteString (ByteString)
import Data.Attoparsec.ByteString
import Data.Attoparsec.Combinator
import Data.Attoparsec.ByteString.Char8

type Identifier = Text

reservedKeywords :: [String]
reservedKeywords =
  [ "let", "in", "case", "return", "of", "inl", "inr" , "fst" , "snd" , ";", "unit", "exfalso" ]

pIdentifier :: Parser Identifier
pIdentifier = do
  id <- many1' letter_ascii
  guard (id `notElem` reservedKeywords)
  return $ Data.Text.pack id

data CheckF b =
    Lam Identifier (CheckF b)
  | Let Pattern (InferF b) (CheckF b)
  | One
  | Prd (CheckF b) (CheckF b)
  | Inl (CheckF b)
  | Inr (CheckF b)
  | Neu (InferF b)
  deriving (Show, Functor, Foldable, Traversable)

type RCheck = CheckF String
type Check  = CheckF Integer

pRCheck :: Parser RCheck
pRCheck = Lam <$> (string "\\" *> skipSpace
               *> pIdentifier <* betweenSpace (string "."))
              <*> pRCheck
      <|> Let <$> (string "let" *> betweenSpace pPattern)
              <*> (string "="   *> betweenSpace pRInfer)
              <*> (string "in"  *> skipSpace *> pRCheck)
      <|> One <$  string "unit"
      <|> Prd <$> (string "(" *> betweenSpace pRCheck)
              <*> (string "," *> betweenSpace pRCheck <* string ")")
      <|> Inl <$> (string "inl" *> skipSpace *> pRCheck)
      <|> Inr <$> (string "inr" *> skipSpace *> pRCheck)
      <|> Neu <$> pRInfer2

data InferF b =
    Var Identifier
  | App (InferF b) (CheckF b)
  | Skp (CheckF b) (InferF b)
  | Fst (InferF b)
  | Snd (InferF b)
  | Cas (InferF b) (TypeF b) Identifier (CheckF b) Identifier (CheckF b)
  | ExF (TypeF b) (InferF b)
  | Cut (CheckF b) (TypeF b) 
  deriving (Show, Functor, Foldable, Traversable)

type RInfer = InferF String
type Infer  = InferF Integer

pRInfer :: Parser RInfer
pRInfer = Skp <$> pRCheck <* betweenSpace (string ";")
              <*> pRInfer
      <|> pRInfer2


chainl1 :: Parser a -> Parser b -> Parser (a -> b -> a) -> Parser a
chainl1 p q op = p >>= rest
  where rest x = (op <*> return x <*> q >>= rest) <|> return x

pRInfer2 :: Parser RInfer
pRInfer2 = (chainl1 pRInfer3 pRCheck $ App <$ string " " <* skipSpace)
       <|> pRInfer3

pRInfer3 :: Parser RInfer
pRInfer3 = Fst <$> (string "fst" *> skipSpace *> pRInfer)
       <|> Snd <$> (string "snd" *> skipSpace *> pRInfer)
       <|> Cut <$> (string "(" *> betweenSpace pRCheck)
               <*> (string ":" *> betweenSpace pRType <* string ")")
       <|> Cas <$> (string "case"   *> betweenSpace pRInfer)
               <*> (string "return" *> betweenSpace pRType)
               <*> (string "of"     *> betweenSpace pIdentifier)
               <*> (string "->"     *> betweenSpace pRCheck)
               <*> (string "|"      *> betweenSpace pIdentifier)
               <*> (string "->"     *> skipSpace *> pRCheck)
       <|> ExF <$> (string "exfalso" *> betweenSpace pRType)
               <*> (betweenSpace pRInfer)
       <|> Var <$> pIdentifier
       <|> string "(" *> skipSpace *> pRInfer <* skipSpace <* string ")"

data Pattern =
    All Identifier
  | And Pattern Pattern
  deriving Show

pPattern2 :: Parser Pattern
pPattern2 = And <$> pPattern  <* skipSpace
                <* string "," <* skipSpace
               <*> pPattern2
       <|> pPattern

pPattern :: Parser Pattern
pPattern = All <$> pIdentifier
       <|> string "(" *> pPattern2 <* string ")"

pRProblem :: Parser (RType, RCheck)
pRProblem = (,) <$> (pRType <* betweenSpace (string ":"))
               <*> pRCheck

newtype IPair f g a = IPair { runIPair :: (f a, g a) }
  deriving (Functor, Foldable, Traversable)

pProblem :: Parser (Type , Check)
pProblem = fmap runIPair $ reifyNames $ fmap IPair pRProblem

fromRight :: Either a b -> Maybe b
fromRight = either (const Nothing) Just

parseProblem :: ByteString -> Maybe (Type , Check)
parseProblem = fromRight . parseOnly (pProblem <* skipSpace <* endOfInput)

parseProblems :: ByteString -> Maybe [(Type, Check)]
parseProblems = fromRight . parseOnly (many (pProblem <* skipSpace) <* endOfInput)
