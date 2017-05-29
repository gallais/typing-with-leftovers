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
  [ "let", "in", "case", "return", "of", "inl", "inr" , "fst" , "snd" , "exfalso" ]

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
      <|> One <$  string "()"
      <|> Prd <$> (string "(" *> betweenSpace pRCheck)
              <*> (string "," *> betweenSpace pRCheck <* string ")")
      <|> Inl <$> (string "inl" *> skipSpace *> pRCheck)
      <|> Inr <$> (string "inr" *> skipSpace *> pRCheck)
      <|> Neu <$> pRInfer

data InferF b =
    Var Identifier
  | App (InferF b) (CheckF b)
  | Fst (InferF b)
  | Snd (InferF b)
  | Cas (InferF b) (TypeF b) Identifier (CheckF b) Identifier (CheckF b)
  | ExF (TypeF b) (InferF b)
  | Cut (CheckF b) (TypeF b) 
  deriving (Show, Functor, Foldable, Traversable)

type RInfer = InferF String
type Infer  = InferF Integer

pRVar :: Parser RInfer
pRVar = Var <$> pIdentifier

pRCut :: Parser RInfer
pRCut = Cut <$> (string "(" *> betweenSpace pRCheck)
            <*> (string ":" *> betweenSpace pRType <* string ")")

pRNut :: Parser RInfer
pRNut = pRVar <|> pRCut

pRArg :: Parser RCheck
pRArg = Neu <$> pRVar
    <|> string "(" *> betweenSpace pRCheck <* string ")"

chainl1 :: Parser a -> Parser b -> Parser (a -> b -> a) -> Parser a
chainl1 p q op = p >>= rest
  where rest x = (op <*> return x <*> q >>= rest) <|> return x

pRInfer :: Parser RInfer
pRInfer = (chainl1 pRInfer2 pRArg $ App <$ string " " <* skipSpace)
       <|> pRInfer2

pRInfer2 :: Parser RInfer
pRInfer2 = Fst <$> (string "fst" *> skipSpace *> pRInfer2)
       <|> Snd <$> (string "snd" *> skipSpace *> pRInfer2)
       <|> Cas <$> (string "case"   *> betweenSpace pRInfer)
               <*> (string "return" *> betweenSpace pRType)
               <*> (string "of"     *> betweenSpace pIdentifier)
               <*> (string "->"     *> betweenSpace pRCheck)
               <*> (string "|"      *> betweenSpace pIdentifier)
               <*> (string "->"     *> skipSpace *> pRCheck)
       <|> ExF <$> (string "exfalso" *> skipSpace *> pRType)
               <*> (skipSpace *> pRInfer2)
       <|> pRNut
       <|> string "(" *> skipSpace *> pRInfer <* skipSpace <* string ")"

data Pattern =
    All Identifier
  | Uni
  | And Pattern Pattern
  deriving Show

pPattern2 :: Parser Pattern
pPattern2 = And <$> pPattern  <* skipSpace
                <* string "," <* skipSpace
               <*> pPattern2
       <|> Uni <$  string "()"
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
