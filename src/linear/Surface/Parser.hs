{-# LANGUAGE OverloadedStrings #-}
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
  [ "let", "in", "case", "return", "of", "inl", "inr" , "fst" , "snd" ]

pIdentifier :: Parser Identifier
pIdentifier = do
  id <- many1' letter_ascii
  guard (id `notElem` reservedKeywords)
  return $ Data.Text.pack id

data Check =
    Lam Identifier Check
  | Let Pattern Infer Check
  | Prd Check Check
  | Inl Check
  | Inr Check
  | Neu Infer
  deriving Show

pCheck :: Parser Check
pCheck = Lam <$> (string "\\" *> skipSpace
              *> pIdentifier <* betweenSpace (string "."))
             <*> pCheck
     <|> Let <$> (string "let" *> betweenSpace pPattern)
             <*> (string "="   *> betweenSpace pInfer)
             <*> (string "in"  *> skipSpace *> pCheck)
     <|> Prd <$> (string "(" *> betweenSpace pCheck)
             <*> (string "," *> betweenSpace pCheck <* string ")")
     <|> Inl <$> (string "inl" *> skipSpace *> pCheck)
     <|> Inr <$> (string "inr" *> skipSpace *> pCheck)
     <|> Neu <$> pInfer

data Infer =
    Var Identifier
  | App Infer Check
  | Fst Infer
  | Snd Infer
  | Cas Infer Type Identifier Check Identifier Check
  | Cut Check Type 
  deriving Show

chainl1 :: Parser a -> Parser b -> Parser (a -> b -> a) -> Parser a
chainl1 p q op = p >>= rest
  where rest x = (op <*> return x <*> q >>= rest) <|> return x

pInfer :: Parser Infer
pInfer = chainl1 pInfer2 pCheck $ App <$ string " " <* skipSpace

pInfer2 :: Parser Infer
pInfer2 = Fst <$> (string "fst" *> skipSpace *> pInfer)
      <|> Snd <$> (string "snd" *> skipSpace *> pInfer)
      <|> Cut <$> (string "(" *> betweenSpace pCheck)
              <*> (string ":" *> betweenSpace pType <* string ")")
      <|> Cas <$> (string "case"   *> betweenSpace pInfer)
              <*> (string "return" *> betweenSpace pType)
              <*> (string "of"     *> betweenSpace pIdentifier)
              <*> (string "->"     *> betweenSpace pCheck)
              <*> (string "|"      *> betweenSpace pIdentifier)
              <*> (string "->"     *> skipSpace *> pCheck)
      <|> Var <$> pIdentifier

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

pProblem :: Parser (Type , Check)
pProblem = (,) <$> (pType <* betweenSpace (string ":"))
               <*> pCheck

fromRight :: Either a b -> Maybe b
fromRight = either (const Nothing) Just

parseProblem :: ByteString -> Maybe (Type , Check)
parseProblem = fromRight . parseOnly (pProblem <* skipSpace <* endOfInput)

parseProblems :: ByteString -> Maybe [(Type, Check)]
parseProblems = fromRight . parseOnly (many (pProblem <* skipSpace) <* endOfInput)
